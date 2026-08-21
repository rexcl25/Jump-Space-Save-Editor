using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Net;
using System.Reflection;
using System.Text;
using System.Text.RegularExpressions;
using System.Threading;
using MelonLoader;
using UnityEngine.InputSystem;
using Il2CppInterop.Runtime;
// Deliberately NOT "using HarmonyLib;" - the referenced 0Harmony.dll also
// exposes a namespace literally called "Harmony" (legacy Harmony 1.x
// layout) that shadows the class import and breaks bare "Harmony"/
// "HarmonyMethod" references (confirmed via a real build error). Harmony
// types are fully qualified as HarmonyLib.Harmony / HarmonyLib.HarmonyMethod
// at their use sites instead.

[assembly: MelonInfo(typeof(JumpSpaceEditor.EditorMod), "JumpSpace Blueprint Editor", "0.1.0", "you")]
[assembly: MelonColor(60, 255, 160, 60)]

namespace JumpSpaceEditor
{
    /// <summary>
    /// STAGE 2 mod: actually changes your owned blueprints (assembler storage).
    ///
    /// Design notes (read before using):
    /// - LEVEL changes go through the game's own MetaProgressionManager.TryUpgradeBlueprint /
    ///   TryModifyBlueprintModuleLevel methods - the same code path the in-game UI uses,
    ///   so it validates/behaves exactly like a normal upgrade (just without needing to
    ///   grind currency - we hand you a pile of credits first).
    /// - RARITY has no official upgrade path in this game at all (confirmed via full
    ///   method dump of MetaProgressionManager). Setting it is a direct reflection write
    ///   to GeneratedItem.m_Rarity / GeneratedModule.m_Rarity. This is unofficial: no
    ///   validation, no currency cost, and it's the one thing the community has flagged
    ///   as more likely to cause a crash or weirdness. Save your game / back up your
    ///   Steam Cloud save before using it, and test on one item first.
    /// - No on-screen UI (avoids depending on Unity's IMGUI module, which some builds
    ///   strip out if the shipped game never calls OnGUI itself). Everything is
    ///   keyboard-driven; all feedback goes to the MelonLoader console and to
    ///   Editor_Log.txt next to this DLL.
    ///
    /// Controls: only 4 keybinds total, F5-F8, everything else lives in the
    /// web UI.
    ///   F5 (browser tab only, see EditorUI.html) - Refresh
    ///   F6          - force save now (SaveDataToCloud)
    ///   F7          - add 25,000 credits
    ///   F8          - add to every ingot tier at once (Crude +20, Flawed +15,
    ///                 Pure +10, Flawless +5, Pristine +1 - least rare gets
    ///                 the biggest bump, most rare gets the smallest)
    ///
    /// There's also a real web UI: once the game is running with this mod loaded,
    /// open http://localhost:8765/ in any browser (a second monitor works great).
    /// It talks to a tiny local HTTP server this mod runs inside the game process
    /// (loopback-only, so no firewall prompt). All the actual game-touching work
    /// still happens on Unity's main thread - the HTTP thread just queues requests
    /// and waits for the main thread to process them each frame, which is required
    /// for IL2CPP object safety.
    /// </summary>
    public class EditorMod : MelonMod
    {
        private Type _mgrType;
        private Type _itemRarityType;
        private Type _itemModuleScriptableType;
        private Type _itemGeneratorType;
        private static readonly Random _rerollRng = new Random();
        private int _selectedBlueprintIndex = 0;
        private int _selectedModuleIndex = -1; // -1 = whole item

        private class ModuleCandidate
        {
            public string Guid;
            public string DisplayName;
            public object Scriptable;
            // Item TEMPLATE guids (GeneratedItem.m_TemplateGuid, e.g. "Sector
            // Scanner"), not module guids. Empty AllowedTemplateGuids means
            // "no allow-list restriction" (compatible with anything not on
            // the forbidden list). Populated in RefreshModuleCandidates from
            // m_AllowedItems/m_ForbiddenItems (List<AssetReference>).
            public List<string> AllowedTemplateGuids = new List<string>();
            public List<string> ForbiddenTemplateGuids = new List<string>();
            // ItemModuleScriptable.m_IsBasicModule - this is what the game
            // itself actually uses to decide "Upgradeable Features" (basic)
            // vs "Custom Modules" (non-basic) section placement, confirmed
            // via the sample dump ("Improved damage": m_IsBasicModule=True).
            // Slot ARRAY INDEX alone (our < FixedUpgradeableModuleCount
            // convention) only happens to line up with this on unmodified
            // items - anything we newly construct has to match on this flag
            // explicitly or the game will file it under the wrong section.
            public bool IsBasicModule;
        }

        private readonly List<ModuleCandidate> _moduleCandidates = new List<ModuleCandidate>();
        private int _selectedCandidateIndex = -1;

        // Catalog entry for one cosmetic (scope, color swap, etc.) - read
        // from PersistentScriptableLibrary.AllCosmetics. SlotType determines
        // which CosmeticSelection slots it's a valid pick for (e.g. only
        // "Scope"-typed cosmetics belong in a "Scope"-typed slot).
        private class CosmeticCandidate
        {
            public string Guid;
            public string DisplayName;
            public string SlotType;
            public bool IsAttachment;
        }
        private readonly List<CosmeticCandidate> _cosmeticCandidates = new List<CosmeticCandidate>();

        // Template guid -> the item's real/original display name (e.g.
        // "Ironbelt LMG"), independent of whatever custom name you've given
        // it in-game (ResolvedName/m_CustomName show the custom name once
        // set, with no way to see the original alongside it). Populated from
        // two catalog sources, both keyed by the same guid GeneratedItem.
        // m_TemplateGuid uses: weapon templates via
        // PersistentScriptableLibrary.m_WeaponEntriesByGuid (confirmed the
        // dictionary's key matches its own entry's m_Data.m_AssetGUID) and
        // ship components via AllShipComponents (each has its own
        // m_AssetGUID + ItemDisplayText directly).
        private readonly Dictionary<string, string> _templateOriginalNames = new Dictionary<string, string>();

        // InventoryItem.m_GUID -> display name, for carried items whose
        // m_GeneratedData is NOT a real generated item (m_TemplateGuid/
        // m_Guid/m_Modules/m_Cosmetics all null, IsGenerated=False, so
        // ResolvedName comes back null) - confirmed via a real log to be
        // consumables/craftables (e.g. "Med EM-8"). Their own m_GUID is a
        // lookup key into
        // Il2CppKeepsake.GameplayFeatures.Assembler.CraftablesLibrary
        // .LazyUnlockToCraftable (Dictionary<string, Craftable>), found via
        // "Inspect Consumable/Pickup Name Catalog" - Craftable.DisplayName
        // gives the real name (e.g. key "66ff81b55f59c70419a67f811aa2ac14"
        // -> Craftable.DisplayName "Med EM-8", asset name
        // "Blueprint_Item_Medimate_Waves").
        private readonly Dictionary<string, string> _craftableNamesByGuid = new Dictionary<string, string>();

        // Craftable.m_Category (CraftableCategory, unexpanded) per guid - only
        // used to filter the "Change Consumable" swap catalog down to real
        // consumables, NOT for name resolution (that stays unfiltered so any
        // owned item's name still resolves regardless of category). Populated
        // alongside _craftableNamesByGuid in RefreshCraftableNames.
        private readonly Dictionary<string, string> _craftableCategoryByGuid = new Dictionary<string, string>();

        // The category value(s) actually seen among KnownConsumableGuids
        // below - computed once per RefreshCraftableNames, used as an
        // empirical whitelist instead of guessing what the CraftableCategory
        // enum's member names mean (its internal Unity asset-name convention
        // prefixes EVERY entry with "Blueprint_", including confirmed real
        // consumables like Med EM-8 - "Blueprint_Item_Medimate_Waves" - so
        // string-matching for "blueprint" would wrongly exclude consumables
        // too). Empty if none of the known guids turned up this session, in
        // which case filtering falls back to "show everything" rather than
        // guessing.
        private readonly HashSet<string> _consumableCategoryWhitelist = new HashSet<string>();

        // Guids of consumables CONFIRMED real via actual user deep-dump logs
        // (owned InventoryItems with IsGenerated=False whose m_GUID resolved
        // a sensible name through this exact catalog) - Med EM-8 plus 5 other
        // distinct consumables sampled across two separate log uploads. Not a
        // guess: every one of these was directly observed in a real carried
        // inventory slot.
        private static readonly string[] KnownConsumableGuids =
        {
            "66ff81b55f59c70419a67f811aa2ac14", // Med EM-8
            "ca554bae681cb4840bdd184572739182",
            "5469beec12c8fed4bbe3845eb5308cde",
            "7b05530defaeb7345974689e91b76142",
            "ef8bf56f8d0fb3148b394c1b389f44af",
            "af37342b553ca20458ff9836456f17b5",
        };

        // Full "change base item to ANY template the game has" catalog - not
        // just items you already own (that's templateCandidatesFor() client-
        // side, kept as a fallback). Weapons are always confidently
        // categorized (m_WeaponEntriesByGuid is exclusively on-foot guns, so
        // Category="Weapons" always). Ship components used to read
        // Category=null here (no confirmed per-entry category signal from
        // live discovery) - now categorized via StaticItemCategoryByGuid, a
        // guid->category table cross-referenced from JumpSaves' independently
        // reverse-engineered static catalog (see that dictionary's comment,
        // near RefreshItemTemplateCatalog). Only falls back to null for a
        // guid that table doesn't recognize (a genuinely new/unseen
        // template). TypeName still carries each entry's raw IL2Cpp runtime
        // type name for reference.
        private class ItemTemplateCandidate
        {
            public string Guid;
            public string DisplayName;
            public string Category;
            public string TypeName;
        }
        private readonly List<ItemTemplateCandidate> _itemTemplateCandidates = new List<ItemTemplateCandidate>();

        // Captures each module's guid/rarity/level/rolls the FIRST time we ever
        // see it (i.e. as it was in your save before any edits this session),
        // keyed by blueprint guid + module index, so "Reset to Original" has
        // something to restore to. Populated lazily as blueprints get listed
        // (BuildBlueprintsJson), never overwritten once set.
        private class ModuleSnapshot
        {
            public string ModuleGuid;
            public string Rarity;
            public int UpgradeLevel;
            public float[] Rolls;
        }
        private readonly Dictionary<string, ModuleSnapshot> _originalModuleSnapshots = new Dictionary<string, ModuleSnapshot>();

        // Same idea as ModuleSnapshot, but for the ITEM itself (rarity +
        // level) - captured the first time each blueprint is listed, keyed
        // by blueprint guid. Powers the global "Reset Everything" button.
        // Deliberately doesn't store a module count: restoring rarity and
        // then re-running ResizeModulesForRarity for that same rarity name
        // recomputes the correct original module count from first
        // principles (basic-slot count read off the item + that rarity's
        // custom-slot count), which is simpler and can't drift out of sync.
        private class ItemSnapshot
        {
            public string Rarity;
            public int Level;
            // Captured so "Reset Everything" can undo a Change Base Item too,
            // not just rarity/level - the per-module ModuleSnapshots already
            // restore each slot's exact original module guid/rarity/level/
            // rolls, so simply putting the template guid back is enough (no
            // need to re-run RebuildModulesForNewTemplate on reset).
            public string TemplateGuid;
            // Inventory-only: a consumable's own m_GUID (its "type"), captured
            // so "Reset Everything" can undo a Change Consumable swap the same
            // way TemplateGuid undoes a blueprint's Change Base Item. Null for
            // blueprints and for gear-type inventory items (they use
            // TemplateGuid instead).
            public string ConsumableGuid;
        }
        private readonly Dictionary<string, ItemSnapshot> _originalItemSnapshots = new Dictionary<string, ItemSnapshot>();

        // Same idea again, for one CosmeticSelection slot (e.g. a weapon's
        // Scope slot) - just the guid, since slot type/index never change,
        // only which cosmetic is plugged into the slot. Keyed the same way
        // as ModuleSnapshot (blueprint guid + index).
        private class CosmeticSnapshot
        {
            public string CosmeticGuid;
        }
        private readonly Dictionary<string, CosmeticSnapshot> _originalCosmeticSnapshots = new Dictionary<string, CosmeticSnapshot>();

        // Credits + each ingot's amount, captured once the first time
        // currencies read back as "real" (see CurrenciesLookReal) - null
        // until then, so we never snapshot the bogus all-zero readings you
        // can get before a save has actually loaded.
        private Dictionary<string, int> _originalCurrencySnapshot;

        // Flip to false if you'd rather open the tab yourself.
        private const bool AutoOpenWebUiOnLaunch = true;

        private const int HttpPort = 8765;
        private HttpListener _httpListener;
        private Thread _httpThread;

        // Hotbar refresh trace (see StartHotbarRefreshTrace) - Harmony
        // instance and per-label throttle timestamps live at class scope so
        // the trace can be started from one HTTP request and keep logging
        // asynchronously (from whatever thread the game calls these getters
        // on) until explicitly stopped.
        // Fully qualified (HarmonyLib.Harmony, not bare "Harmony") because
        // the referenced 0Harmony.dll apparently also exposes a namespace
        // literally called "Harmony" (legacy Harmony 1.x layout) that shadows
        // the "using HarmonyLib;" class import - confirmed via a real build
        // error (CS0118: 'Harmony' is a namespace but is used like a type).
        private HarmonyLib.Harmony _hotbarTraceHarmony;
        private static readonly Dictionary<string, DateTime> _hotbarTraceLastLogAt = new Dictionary<string, DateTime>();

        private class PendingRequest
        {
            public HttpListenerContext Context;
            public ManualResetEventSlim Done = new ManualResetEventSlim(false);
        }

        private readonly Queue<PendingRequest> _pendingRequests = new Queue<PendingRequest>();
        private readonly object _queueLock = new object();

        public override void OnLateInitializeMelon()
        {
            MelonLogger.Msg("JumpSpace Blueprint Editor loaded.");
            _mgrType = FindType("Il2CppKeepsake.MetaProgression.MetaProgressionManager");
            if (_mgrType == null)
            {
                MelonLogger.Error("Could not find MetaProgressionManager - editor will not function.");
                return;
            }
            MelonLogger.Msg("Everything (item edits, debug dumps, currencies) lives in the web UI now - open http://localhost:8765/ .");
            MelonLogger.Msg("Only 4 keybinds, F5-F8: F5 in the browser tab = Refresh, F6 = force save, F7 = +25,000 credits, F8 = +ingots (all 5 tiers at once).");
            StartWebServer();

            if (AutoOpenWebUiOnLaunch && _httpListener != null && _httpListener.IsListening)
            {
                try
                {
                    // UseShellExecute=true is required on .NET Core/5+/6+ to
                    // hand a URL off to the OS's default-browser association -
                    // without it, Process.Start tries to execute the URL
                    // string as a program and throws.
                    Process.Start(new ProcessStartInfo
                    {
                        FileName = $"http://localhost:{HttpPort}/",
                        UseShellExecute = true
                    });
                    Log("Auto-opened the web UI in your default browser.");
                }
                catch (Exception ex)
                {
                    Log("Could not auto-open the web UI in a browser: " + ex.Message + " - open it manually at http://localhost:" + HttpPort + "/");
                }
            }
        }

        public override void OnApplicationQuit()
        {
            try { _httpListener?.Stop(); _httpListener?.Close(); } catch { }
        }

        // ---------- web UI server ----------

        private void StartWebServer()
        {
            try
            {
                _httpListener = new HttpListener();
                _httpListener.Prefixes.Add($"http://localhost:{HttpPort}/");
                _httpListener.Start();
                _httpThread = new Thread(HttpLoop) { IsBackground = true };
                _httpThread.Start();
                Log($"Web UI running - open http://localhost:{HttpPort}/ in a browser (works great on a second monitor).");
            }
            catch (Exception ex)
            {
                Log("Could not start web UI server: " + ex.Message);
            }
        }

        // Runs on its own background thread. Only touches raw sockets/HTTP -
        // never the game/IL2CPP objects directly, since those aren't safe to
        // touch off Unity's main thread. Each request gets queued and this
        // thread blocks until the main thread (via OnUpdate) has processed it
        // and written the response.
        private void HttpLoop()
        {
            while (_httpListener != null && _httpListener.IsListening)
            {
                HttpListenerContext ctx;
                try { ctx = _httpListener.GetContext(); }
                catch { break; }

                var pending = new PendingRequest { Context = ctx };
                lock (_queueLock) { _pendingRequests.Enqueue(pending); }
                pending.Done.Wait(5000);
            }
        }

        private void ProcessPendingHttpRequests()
        {
            while (true)
            {
                PendingRequest pending;
                lock (_queueLock)
                {
                    if (_pendingRequests.Count == 0) break;
                    pending = _pendingRequests.Dequeue();
                }
                try { ProcessHttpRequestOnMainThread(pending.Context); }
                catch (Exception ex)
                {
                    // Log this to our own file/console too, not just the HTTP
                    // response - an unhandled exception here used to disappear
                    // silently as far as Editor_Log.txt was concerned, which is
                    // exactly what made an earlier bug (an uncaught reflection
                    // exception deep in a helper method) so hard to track down.
                    Log($"Unhandled exception processing {pending.Context.Request.Url}: {ex}");
                    try { WriteJson(pending.Context, 500, "{\"error\":" + JsonStr(ex.Message) + "}"); } catch { }
                }
                finally { pending.Done.Set(); }
            }
        }

        private void ProcessHttpRequestOnMainThread(HttpListenerContext ctx)
        {
            string path = ctx.Request.Url.AbsolutePath;
            string method = ctx.Request.HttpMethod;

            if (method == "GET" && (path == "/" || path == "/index.html")) { ServeStaticFile(ctx, "EditorUI.html", "text/html"); return; }
            if (method == "GET" && path == "/api/blueprints") { WriteJson(ctx, 200, BuildBlueprintsJson()); return; }
            if (method == "GET" && path == "/api/currencies") { WriteJson(ctx, 200, BuildCurrenciesJson()); return; }
            if (method == "GET" && path == "/api/gameState") { WriteJson(ctx, 200, BuildGameStateJson()); return; }
            if (method == "GET" && path == "/api/moduleTypes") { WriteJson(ctx, 200, BuildModuleTypesJson()); return; }
            if (method == "GET" && path == "/api/cosmeticTypes") { WriteJson(ctx, 200, BuildCosmeticTypesJson()); return; }
            if (method == "GET" && path == "/api/itemTemplates") { WriteJson(ctx, 200, BuildItemTemplateCatalogJson()); return; }
            if (method == "GET" && path == "/api/blueprintSlotCapacities") { WriteJson(ctx, 200, BuildBlueprintSlotCapacitiesJson()); return; }
            if (method == "GET" && path == "/api/inventory") { WriteJson(ctx, 200, BuildInventoryJson()); return; }
            if (method == "GET" && path == "/api/consumableTemplates") { WriteJson(ctx, 200, BuildConsumableTemplateCatalogJson()); return; }
            if (method == "POST" && path == "/api/swapConsumable") { HandleSwapConsumable(ctx); return; }
            if (method == "POST" && path == "/api/inventorySetAmount") { HandleInventorySetAmount(ctx); return; }
            if (method == "POST" && path == "/api/inventorySetAmmo") { HandleInventorySetAmmo(ctx); return; }
            if (method == "POST" && path == "/api/inventorySetLevel") { HandleInventorySetLevel(ctx); return; }
            if (method == "POST" && path == "/api/inventorySetRarity") { HandleInventorySetRarity(ctx); return; }
            if (method == "POST" && path == "/api/inventorySwapModule") { HandleInventorySwapModule(ctx); return; }
            if (method == "POST" && path == "/api/inventoryRerollModule") { HandleInventoryRerollModule(ctx); return; }
            if (method == "POST" && path == "/api/setInventoryModuleRoll") { HandleSetInventoryModuleRoll(ctx); return; }
            if (method == "POST" && path == "/api/inventoryResetModule") { HandleInventoryResetModule(ctx); return; }
            if (method == "POST" && path == "/api/inventoryResetAllModules") { HandleInventoryResetAllModules(ctx); return; }
            if (method == "POST" && path == "/api/inventorySwapCosmetic") { HandleInventorySwapCosmetic(ctx); return; }
            if (method == "POST" && path == "/api/inventoryResetCosmetic") { HandleInventoryResetCosmetic(ctx); return; }
            if (method == "POST" && path == "/api/inventoryResetItem") { HandleInventoryResetItem(ctx); return; }
            if (method == "GET" && path == "/api/inventoryDebugDump") { HandleInventoryDebugDump(ctx); return; }
            if (method == "POST" && path == "/api/swapCosmetic") { HandleSwapCosmetic(ctx); return; }
            if (method == "POST" && path == "/api/resetCosmetic") { HandleResetCosmetic(ctx); return; }
            if (method == "POST" && path == "/api/upgradeLevel") { HandleUpgradeLevel(ctx); return; }
            if (method == "POST" && path == "/api/setLevel") { HandleSetLevel(ctx); return; }
            if (method == "POST" && path == "/api/setRarity") { HandleSetRarity(ctx); return; }
            if (method == "POST" && path == "/api/setCurrency") { HandleSetCurrency(ctx); return; }
            if (method == "POST" && path == "/api/swapModule") { HandleSwapModule(ctx); return; }
            if (method == "POST" && path == "/api/resetModule") { HandleResetModule(ctx); return; }
            if (method == "POST" && path == "/api/resetAllModules") { HandleResetAllModules(ctx); return; }
            if (method == "POST" && path == "/api/rerollModule") { HandleRerollModule(ctx); return; }
            if (method == "POST" && path == "/api/setModuleRoll") { HandleSetModuleRoll(ctx); return; }
            if (method == "POST" && path == "/api/normalizeModuleCount") { HandleNormalizeModuleCount(ctx); return; }
            if (method == "GET" && path == "/api/dumpCategories") { DumpAllBlueprintCategories(); WriteJson(ctx, 200, "{\"ok\":true,\"note\":\"check the MelonLoader console or Editor_Log.txt\"}"); return; }
            if (method == "GET" && path == "/api/dumpModuleCompatibility") { DumpModuleCompatibility(); WriteJson(ctx, 200, "{\"ok\":true,\"note\":\"check the MelonLoader console or Editor_Log.txt\"}"); return; }
            if (method == "GET" && path == "/api/dumpModuleKinds") { DumpModuleKinds(); WriteJson(ctx, 200, "{\"ok\":true,\"note\":\"check the MelonLoader console or Editor_Log.txt\"}"); return; }
            if (method == "GET" && path == "/api/dumpModuleValueRangeDiscovery") { DumpModuleValueRangeDiscovery(); WriteJson(ctx, 200, "{\"ok\":true,\"note\":\"check the MelonLoader console or Editor_Log.txt\"}"); return; }
            if (method == "GET" && path == "/api/dumpItemTemplateDiscovery") { DumpItemTemplateDiscovery(); WriteJson(ctx, 200, "{\"ok\":true,\"note\":\"check the MelonLoader console or Editor_Log.txt\"}"); return; }
            if (method == "GET" && path == "/api/dumpScopeAttachmentDiscovery") { DumpScopeAttachmentDiscovery(); WriteJson(ctx, 200, "{\"ok\":true,\"note\":\"check the MelonLoader console or Editor_Log.txt\"}"); return; }
            if (method == "GET" && path == "/api/dumpCosmeticsScopeDiscovery") { DumpCosmeticsScopeDiscovery(); WriteJson(ctx, 200, "{\"ok\":true,\"note\":\"check the MelonLoader console or Editor_Log.txt\"}"); return; }
            if (method == "GET" && path == "/api/dumpCosmeticSelectionDiscovery") { DumpCosmeticSelectionDiscovery(); WriteJson(ctx, 200, "{\"ok\":true,\"note\":\"check the MelonLoader console or Editor_Log.txt\"}"); return; }
            if (method == "POST" && path == "/api/save") { SaveNow(); WriteJson(ctx, 200, "{\"ok\":true}"); return; }
            if (method == "GET" && path == "/api/backups") { WriteJson(ctx, 200, BuildBackupsJson()); return; }
            if (method == "POST" && path == "/api/backups/create") { HandleCreateBackup(ctx); return; }
            if (method == "POST" && path == "/api/backups/restore") { HandleRestoreBackup(ctx); return; }
            if (method == "GET" && path == "/api/cheatMode") { WriteJson(ctx, 200, BuildCheatModeJson()); return; }
            if (method == "POST" && path == "/api/cheatMode") { HandleSetCheatMode(ctx); return; }
            if (method == "POST" && path == "/api/setModuleLevel") { HandleSetModuleLevel(ctx); return; }
            if (method == "POST" && path == "/api/setInventoryModuleLevel") { HandleSetInventoryModuleLevel(ctx); return; }
            if (method == "GET" && path == "/api/debugDump") { HandleDebugDump(ctx); return; }
            if (method == "GET" && path == "/api/searchModuleDatabase") { HandleSearchModuleDatabase(ctx); return; }
            if (method == "GET" && path == "/api/diagnoseUserData") { DiagnoseUserDataStability(); WriteJson(ctx, 200, "{\"ok\":true,\"note\":\"check the MelonLoader console or Editor_Log.txt\"}"); return; }
            if (method == "GET" && path == "/api/dumpItemGenerator") { DumpItemGeneratorShape(); WriteJson(ctx, 200, "{\"ok\":true,\"note\":\"check the MelonLoader console or Editor_Log.txt\"}"); return; }
            if (method == "POST" && path == "/api/resetEverything") { HandleResetEverything(ctx); return; }
            if (method == "POST" && path == "/api/changeItemTemplate") { HandleChangeItemTemplate(ctx); return; }
            if (method == "POST" && path == "/api/duplicateBlueprint") { HandleDuplicateBlueprint(ctx); return; }
            if (method == "POST" && path == "/api/deleteBlueprint") { HandleDeleteBlueprint(ctx); return; }
            if (method == "GET" && path == "/api/dumpWeaponShipTemplateCatalog") { DumpWeaponAndShipTemplateCatalog(); WriteJson(ctx, 200, "{\"ok\":true,\"note\":\"check the MelonLoader console or Editor_Log.txt\"}"); return; }
            if (method == "GET" && path == "/api/dumpInventoryDiscovery") { DumpInventoryDiscovery(); WriteJson(ctx, 200, "{\"ok\":true,\"note\":\"check the MelonLoader console or Editor_Log.txt\"}"); return; }
            if (method == "GET" && path == "/api/dumpArtifactSystemDiscovery") { DumpArtifactSystemDiscovery(); WriteJson(ctx, 200, "{\"ok\":true,\"note\":\"check the MelonLoader console or Editor_Log.txt\"}"); return; }
            if (method == "GET" && path == "/api/dumpBlueprintOrderingDiscovery") { DumpBlueprintOrderingDiscovery(); WriteJson(ctx, 200, "{\"ok\":true,\"note\":\"check the MelonLoader console or Editor_Log.txt\"}"); return; }
            if (method == "GET" && path == "/api/dumpConsumableCatalogDiscovery") { DumpConsumableCatalogDiscovery(); WriteJson(ctx, 200, "{\"ok\":true,\"note\":\"check the MelonLoader console or Editor_Log.txt\"}"); return; }
            if (method == "GET" && path == "/api/dumpConsumableFilterDebug") { DumpConsumableFilterDebug(); WriteJson(ctx, 200, "{\"ok\":true,\"note\":\"check the MelonLoader console or Editor_Log.txt\"}"); return; }
            if (method == "GET" && path == "/api/dumpBlueprintLevelCapDiscovery") { DumpBlueprintLevelCapDiscovery(); WriteJson(ctx, 200, "{\"ok\":true,\"note\":\"check the MelonLoader console or Editor_Log.txt\"}"); return; }
            if (method == "GET" && path == "/api/dumpHotbarGameObjectDiscovery") { DumpHotbarGameObjectDiscovery(); WriteJson(ctx, 200, "{\"ok\":true,\"note\":\"check the MelonLoader console or Editor_Log.txt\"}"); return; }
            if (method == "GET" && path == "/api/dumpPickupSystemDiscovery") { DumpPickupSystemDiscovery(); WriteJson(ctx, 200, "{\"ok\":true,\"note\":\"check the MelonLoader console or Editor_Log.txt\"}"); return; }
            if (method == "GET" && path == "/api/dumpPlayerPickupableItemHandlerDiscovery") { DumpPlayerPickupableItemHandlerDiscovery(); WriteJson(ctx, 200, "{\"ok\":true,\"note\":\"check the MelonLoader console or Editor_Log.txt\"}"); return; }
            if (method == "GET" && path == "/api/tryRefreshHeldItem") { TryRefreshHeldItem(); WriteJson(ctx, 200, "{\"ok\":true,\"note\":\"check the MelonLoader console or Editor_Log.txt\"}"); return; }
            if (method == "GET" && path == "/api/dumpHotbarUIDiscovery") { DumpHotbarUIDiscovery(); WriteJson(ctx, 200, "{\"ok\":true,\"note\":\"check the MelonLoader console or Editor_Log.txt\"}"); return; }
            if (method == "GET" && path == "/api/dumpHotbarUIByValueDiscovery") { DumpHotbarUIByValueDiscovery(); WriteJson(ctx, 200, "{\"ok\":true,\"note\":\"check the MelonLoader console or Editor_Log.txt\"}"); return; }
            if (method == "GET" && path == "/api/dumpHotbarUIByReferenceDiscovery") { DumpHotbarUIByReferenceDiscovery(); WriteJson(ctx, 200, "{\"ok\":true,\"note\":\"check the MelonLoader console or Editor_Log.txt\"}"); return; }
            if (method == "GET" && path == "/api/startHotbarRefreshTrace") { StartHotbarRefreshTrace(); WriteJson(ctx, 200, "{\"ok\":true,\"note\":\"check the MelonLoader console or Editor_Log.txt\"}"); return; }
            if (method == "GET" && path == "/api/stopHotbarRefreshTrace") { StopHotbarRefreshTrace(); WriteJson(ctx, 200, "{\"ok\":true,\"note\":\"check the MelonLoader console or Editor_Log.txt\"}"); return; }

            WriteJson(ctx, 404, "{\"error\":\"not found\"}");
        }

        private string BuildBlueprintsJson()
        {
            var blueprints = GetBlueprintsSnapshot();
            if (_moduleCandidates.Count == 0) RefreshModuleCandidates(false);
            var candidatesByGuid = new Dictionary<string, ModuleCandidate>();
            foreach (var c in _moduleCandidates)
                if (!candidatesByGuid.ContainsKey(c.Guid)) candidatesByGuid[c.Guid] = c;
            if (_cosmeticCandidates.Count == 0) RefreshCosmeticCandidates();
            var cosmeticsByGuid = new Dictionary<string, CosmeticCandidate>();
            foreach (var c in _cosmeticCandidates)
                if (!cosmeticsByGuid.ContainsKey(c.Guid)) cosmeticsByGuid[c.Guid] = c;
            if (_templateOriginalNames.Count == 0) RefreshTemplateOriginalNames();
            var categoryMap = GetCategoryMap();

            var sb = new StringBuilder();
            sb.Append("[");
            for (int i = 0; i < blueprints.Count; i++)
            {
                if (i > 0) sb.Append(",");
                object bp = blueprints[i];
                object generatedData = GetInstanceMemberValue(bp, "m_GeneratedData");
                string name = AsString(GetInstanceMemberValue(generatedData, "ResolvedName"));
                object rarity = GetInstanceMemberValue(generatedData, "m_Rarity");
                object level = GetInstanceMemberValue(generatedData, "m_Level");
                object slot = GetInstanceMemberValue(bp, "m_SlotIndex");
                object guid = GetInstanceMemberValue(bp, "m_Guid");
                string bpGuidStr = guid as string;
                string categoryGuid = GetInstanceMemberValue(bp, "m_CategoryGuid") as string;
                string templateGuid = GetInstanceMemberValue(generatedData, "m_TemplateGuid") as string;
                EnsureItemSnapshot(bpGuidStr, rarity, level, templateGuid);

                // Real official game check, confirmed via a live method dump
                // of MetaProgressionManager (BlueprintIsUpgradeable(Blueprint)
                // -> bool) - not a guessed level-cap formula. Same reasoning
                // as calling TryUpgradeBlueprint itself rather than hand-
                // rolling the upgrade: let the game's own logic decide.
                // Fails open (button stays enabled) if the method can't be
                // found/called, rather than guessing wrong and blocking a
                // legitimate upgrade.
                bool isUpgradeable = true;
                try
                {
                    var canUpgradeMethod = _mgrType?.GetMethod("BlueprintIsUpgradeable", BindingFlags.Public | BindingFlags.Static);
                    if (canUpgradeMethod != null && canUpgradeMethod.Invoke(null, new object[] { bp }) is bool canUpgradeResult)
                        isUpgradeable = canUpgradeResult;
                }
                catch (Exception ex) { Log("BuildBlueprintsJson: BlueprintIsUpgradeable threw: " + ex.Message); }

                // The item's real/original display name (e.g. "Ironbelt LMG"),
                // looked up off its template guid rather than ResolvedName -
                // ResolvedName follows whatever custom name you've given it
                // in-game. Everything in this game can be renamed, so this is
                // always surfaced (not just when it differs from the current
                // name) - there's no reliable way to tell "unrenamed" from
                // "renamed to something that happens to match" otherwise.
                string originalName = null;
                if (templateGuid != null && _templateOriginalNames.TryGetValue(templateGuid, out var origName))
                    originalName = origName;

                string groupName = "Components";
                string categoryName = "Unknown";
                if (name != null && KnownItemCategory.TryGetValue(name, out var knownCategory))
                {
                    categoryName = knownCategory;
                    groupName = knownCategory == "Weapons" ? "Equipment" : "Components";
                }
                else if (categoryGuid != null && categoryMap.TryGetValue(categoryGuid, out var info))
                {
                    groupName = info.group;
                    categoryName = info.name;
                }

                sb.Append("{\"index\":").Append(i)
                  .Append(",\"name\":").Append(JsonStr(name))
                  .Append(",\"originalName\":").Append(JsonStr(originalName))
                  .Append(",\"rarity\":").Append(JsonStr(rarity == null ? null : rarity.ToString()))
                  .Append(",\"level\":").Append(SafeInt(level))
                  .Append(",\"upgradeable\":").Append(isUpgradeable ? "true" : "false")
                  .Append(",\"slot\":").Append(SafeInt(slot))
                  .Append(",\"guid\":").Append(JsonStr(guid as string))
                  .Append(",\"templateGuid\":").Append(JsonStr(templateGuid))
                  .Append(",\"group\":").Append(JsonStr(groupName))
                  .Append(",\"category\":").Append(JsonStr(categoryName))
                  .Append(",\"modules\":[");

                int moduleCount = GetModuleCount(generatedData);
                for (int m = 0; m < moduleCount; m++)
                {
                    if (m > 0) sb.Append(",");
                    object module = GetModuleAt(generatedData, m);
                    object mRarity = GetInstanceMemberValue(module, "m_Rarity");
                    object mLevel = GetInstanceMemberValue(module, "m_UpgradeLevel");
                    string mGuid = GetInstanceMemberValue(module, "m_ModuleGuid") as string;
                    EnsureModuleSnapshot(bpGuidStr, m, module);

                    string moduleName = "(unknown module)";
                    string moduleDesc = "";
                    string rarityRange = null;
                    string tweakablesJson = "[]";
                    int maxLevel = -1;
                    // What section this module actually belongs in per the
                    // game (m_IsBasicModule on its own catalog entry) - NOT
                    // derived from slot index, since that count varies by
                    // item type (Reactors: 1 basic slot; most weapons: 2).
                    bool moduleIsBasic = false;
                    if (mGuid != null && candidatesByGuid.TryGetValue(mGuid, out var candidate))
                    {
                        moduleName = candidate.DisplayName;
                        moduleDesc = TryGetModuleDescription(candidate.Scriptable, mRarity, mLevel, module);
                        rarityRange = GetRarityRangeString(candidate.Scriptable);
                        moduleIsBasic = candidate.IsBasicModule;
                        maxLevel = GetModuleMaxLevel(candidate.Scriptable, mRarity);
                        tweakablesJson = BuildTweakableRangesJson(candidate.Scriptable, mRarity, mLevel, module);
                    }

                    sb.Append("{\"index\":").Append(m)
                      .Append(",\"rarity\":").Append(JsonStr(mRarity == null ? null : mRarity.ToString()))
                      .Append(",\"level\":").Append(SafeInt(mLevel))
                      .Append(",\"maxLevel\":").Append(maxLevel)
                      .Append(",\"guid\":").Append(JsonStr(mGuid))
                      .Append(",\"name\":").Append(JsonStr(moduleName))
                      .Append(",\"description\":").Append(JsonStr(moduleDesc))
                      .Append(",\"staticTitle\":").Append(JsonStr(TryGetStaticModuleTitle(mGuid)))
                      .Append(",\"rarityRange\":").Append(JsonStr(rarityRange))
                      .Append(",\"isBasic\":").Append(moduleIsBasic ? "true" : "false")
                      .Append(",\"tweakables\":").Append(tweakablesJson)
                      .Append("}");
                }
                sb.Append("],\"cosmetics\":[");

                int cosmeticCount = GetCosmeticCount(generatedData);
                for (int c = 0; c < cosmeticCount; c++)
                {
                    if (c > 0) sb.Append(",");
                    object cosmetic = GetCosmeticAt(generatedData, c);
                    object slotType = GetInstanceMemberValue(cosmetic, "m_SlotType");
                    object slotIndex = GetInstanceMemberValue(cosmetic, "m_SlotIndex");
                    string cGuid = GetInstanceMemberValue(cosmetic, "m_CosmeticGuid") as string;
                    EnsureCosmeticSnapshot(bpGuidStr, c, cGuid);



                    string cName = cGuid;
                    if (cGuid != null && cosmeticsByGuid.TryGetValue(cGuid, out var cCandidate)) cName = cCandidate.DisplayName;

                    sb.Append("{\"index\":").Append(c)
                      .Append(",\"slotType\":").Append(JsonStr(slotType == null ? null : slotType.ToString()))
                      .Append(",\"slotIndex\":").Append(SafeInt(slotIndex))
                      .Append(",\"guid\":").Append(JsonStr(cGuid))
                      .Append(",\"name\":").Append(JsonStr(cName))
                      .Append("}");
                }
                sb.Append("]}");
            }
            sb.Append("]");
            return sb.ToString();
        }

        // Same shape as a blueprint card's JSON (name/rarity/level/template/
        // modules/cosmetics all read off m_GeneratedData via the exact same
        // helpers BuildBlueprintsJson uses), plus the two fields unique to a
        // carried item: resourceAmount and ammoInMag. No slot/category here -
        // these aren't sorted into the assembler's category system.
        // Snapshot keys use "inv:{index}" (InvSnapshotKey) instead of a
        // blueprint guid so Reset/Reset All Modules/Reset Everything can find
        // them without colliding with blueprint snapshots.
        private string BuildInventoryJson()
        {
            var items = GetInventorySnapshot();
            if (_moduleCandidates.Count == 0) RefreshModuleCandidates(false);
            var candidatesByGuid = new Dictionary<string, ModuleCandidate>();
            foreach (var c in _moduleCandidates)
                if (!candidatesByGuid.ContainsKey(c.Guid)) candidatesByGuid[c.Guid] = c;
            if (_cosmeticCandidates.Count == 0) RefreshCosmeticCandidates();
            var cosmeticsByGuid = new Dictionary<string, CosmeticCandidate>();
            foreach (var c in _cosmeticCandidates)
                if (!cosmeticsByGuid.ContainsKey(c.Guid)) cosmeticsByGuid[c.Guid] = c;
            if (_templateOriginalNames.Count == 0) RefreshTemplateOriginalNames();
            if (_craftableNamesByGuid.Count == 0) RefreshCraftableNames();

            var sb = new StringBuilder();
            sb.Append("[");
            for (int i = 0; i < items.Count; i++)
            {
                if (i > 0) sb.Append(",");
                object item = items[i];
                string invKey = InvSnapshotKey(i);
                string guid = GetInstanceMemberValue(item, "m_GUID") as string;
                float resourceAmount = 0f;
                try { resourceAmount = Convert.ToSingle(GetInstanceMemberValue(item, "m_ResourceAmount")); } catch { }
                int ammoInMag = SafeInt(GetInstanceMemberValue(item, "m_AmmoInMag"));

                object generatedData = GetInstanceMemberValue(item, "m_GeneratedData");
                string resolvedName = GetInstanceMemberValue(generatedData, "ResolvedName") as string;
                object rarity = GetInstanceMemberValue(generatedData, "m_Rarity");
                object level = GetInstanceMemberValue(generatedData, "m_Level");
                string templateGuid = GetInstanceMemberValue(generatedData, "m_TemplateGuid") as string;

                // Confirmed via a real log: items with an empty m_TemplateGuid
                // aren't "generated" items at all (IsGenerated=False, no
                // modules/cosmetics) - they're consumables/craftables, and
                // ResolvedName comes back null for them. Their own m_GUID
                // resolves instead via CraftablesLibrary.LazyUnlockToCraftable
                // (see RefreshCraftableNames). isConsumable is reported to the
                // client so it doesn't have to guess "is this gear or not"
                // from the absence of rarity/modules.
                bool isConsumable = string.IsNullOrEmpty(templateGuid);
                EnsureItemSnapshot(invKey, rarity, level, templateGuid, isConsumable ? guid : null);
                string name = resolvedName;
                if (string.IsNullOrEmpty(name) && guid != null && _craftableNamesByGuid.TryGetValue(guid, out var craftableName))
                    name = craftableName;
                // Neither a real generated/gear item (no templateGuid) nor a
                // resolvable craftable/consumable (no guid, or a guid that
                // doesn't match anything in CraftablesLibrary) - this is a
                // genuinely unfilled carry slot, not an item we failed to
                // name. Reported separately from the "?" fallback below so
                // the client can show a proper empty-slot placeholder
                // (matching how blueprint slots already work) instead of a
                // broken-looking blank card.
                bool isEmpty = string.IsNullOrEmpty(templateGuid) && string.IsNullOrEmpty(name);
                if (string.IsNullOrEmpty(name)) name = "?";

                string originalName = null;
                if (templateGuid != null && _templateOriginalNames.TryGetValue(templateGuid, out var origName)
                    && !string.Equals(origName, name, StringComparison.Ordinal))
                    originalName = origName;

                sb.Append("{\"index\":").Append(i)
                  .Append(",\"guid\":").Append(JsonStr(guid))
                  .Append(",\"name\":").Append(JsonStr(name))
                  .Append(",\"originalName\":").Append(JsonStr(originalName))
                  .Append(",\"isConsumable\":").Append(isConsumable ? "true" : "false")
                  .Append(",\"isEmpty\":").Append(isEmpty ? "true" : "false")
                  .Append(",\"rarity\":").Append(JsonStr(rarity == null ? null : rarity.ToString()))
                  .Append(",\"level\":").Append(SafeInt(level))
                  .Append(",\"templateGuid\":").Append(JsonStr(templateGuid))
                  .Append(",\"resourceAmount\":").Append(resourceAmount.ToString(System.Globalization.CultureInfo.InvariantCulture))
                  .Append(",\"ammoInMag\":").Append(ammoInMag)
                  .Append(",\"modules\":[");

                int moduleCount = GetModuleCount(generatedData);
                for (int m = 0; m < moduleCount; m++)
                {
                    if (m > 0) sb.Append(",");
                    object module = GetModuleAt(generatedData, m);
                    object mRarity = GetInstanceMemberValue(module, "m_Rarity");
                    object mLevel = GetInstanceMemberValue(module, "m_UpgradeLevel");
                    string mGuid = GetInstanceMemberValue(module, "m_ModuleGuid") as string;
                    EnsureModuleSnapshot(invKey, m, module);

                    string moduleName = "(unknown module)";
                    string moduleDesc = "";
                    string rarityRange = null;
                    string tweakablesJson = "[]";
                    int maxLevel = -1;
                    bool moduleIsBasic = false;
                    if (mGuid != null && candidatesByGuid.TryGetValue(mGuid, out var candidate))
                    {
                        moduleName = candidate.DisplayName;
                        moduleDesc = TryGetModuleDescription(candidate.Scriptable, mRarity, mLevel, module);
                        rarityRange = GetRarityRangeString(candidate.Scriptable);
                        moduleIsBasic = candidate.IsBasicModule;
                        maxLevel = GetModuleMaxLevel(candidate.Scriptable, mRarity);
                        tweakablesJson = BuildTweakableRangesJson(candidate.Scriptable, mRarity, mLevel, module);
                    }

                    sb.Append("{\"index\":").Append(m)
                      .Append(",\"rarity\":").Append(JsonStr(mRarity == null ? null : mRarity.ToString()))
                      .Append(",\"level\":").Append(SafeInt(mLevel))
                      .Append(",\"maxLevel\":").Append(maxLevel)
                      .Append(",\"guid\":").Append(JsonStr(mGuid))
                      .Append(",\"name\":").Append(JsonStr(moduleName))
                      .Append(",\"description\":").Append(JsonStr(moduleDesc))
                      .Append(",\"staticTitle\":").Append(JsonStr(TryGetStaticModuleTitle(mGuid)))
                      .Append(",\"rarityRange\":").Append(JsonStr(rarityRange))
                      .Append(",\"isBasic\":").Append(moduleIsBasic ? "true" : "false")
                      .Append(",\"tweakables\":").Append(tweakablesJson)
                      .Append("}");
                }
                sb.Append("],\"cosmetics\":[");

                int cosmeticCount = GetCosmeticCount(generatedData);
                for (int c = 0; c < cosmeticCount; c++)
                {
                    if (c > 0) sb.Append(",");
                    object cosmetic = GetCosmeticAt(generatedData, c);
                    object slotType = GetInstanceMemberValue(cosmetic, "m_SlotType");
                    object slotIndex = GetInstanceMemberValue(cosmetic, "m_SlotIndex");
                    string cGuid = GetInstanceMemberValue(cosmetic, "m_CosmeticGuid") as string;
                    EnsureCosmeticSnapshot(invKey, c, cGuid);

                    string cName = cGuid;
                    if (cGuid != null && cosmeticsByGuid.TryGetValue(cGuid, out var cCandidate)) cName = cCandidate.DisplayName;

                    sb.Append("{\"index\":").Append(c)
                      .Append(",\"slotType\":").Append(JsonStr(slotType == null ? null : slotType.ToString()))
                      .Append(",\"slotIndex\":").Append(SafeInt(slotIndex))
                      .Append(",\"guid\":").Append(JsonStr(cGuid))
                      .Append(",\"name\":").Append(JsonStr(cName))
                      .Append("}");
                }
                sb.Append("]}");
            }
            sb.Append("]");
            return sb.ToString();
        }

        // Reproduces the exact flavor text the game itself shows (e.g. "Bullets
        // chain to nearby enemies 5 times dealing 80% of the original damage") by
        // calling the module template's own GetLocalizedDescription with this
        // module's actual rarity/level/rolls.
        private string TryGetModuleDescription(object scriptable, object rarity, object level, object module)
        {
            try
            {
                var m = scriptable.GetType().GetMethod("GetLocalizedDescription", BindingFlags.Public | BindingFlags.Instance);
                if (m == null) return "";
                object rolls = GetInstanceMemberValue(module, "m_BaseValueRolls");
                object result = m.Invoke(scriptable, new object[] { rarity, SafeInt(level), rolls });
                return StripRichText(result as string ?? "");
            }
            catch { return ""; }
        }

        // Per Cameron: "there seems to be some variation to each module
        // stat... like a range of numbers that stat can be" - confirmed real
        // via DumpModuleValueRangeDiscovery (e.g. a real "Total Damage"
        // tweakable resolved to a genuine 150-200 range, not a fixed
        // number). This exposes that same range to the GUI: for each of a
        // module's tweakable stats, calls the official
        // ItemModuleTweakableValue.CalculateRolledValue(roll, upgradeLevel)
        // - same method Reroll already uses to pick a value - at roll=0 and
        // roll=1 to get the true low/high ends at the module's CURRENT
        // upgrade level (not the raw min/max fields, which don't yet
        // account for m_ValuePerUpgrade). low==high just means this
        // particular stat has no real variation (e.g. its max field is
        // unused/0) - not a bug, some stats are simply constant.
        //
        // Also reports each tweakable's own index within the module's
        // m_BaseValueRolls array (confirmed - by DumpModuleValueRangeDiscovery
        // - to line up 1:1 with GetTweakableValuesForRarity's own entry
        // order), its current raw 0-1 roll, and the resulting current value -
        // this is what lets the GUI show a slider that directly sets a
        // specific roll (see SetModuleRollValue / HandleSetModuleRoll).
        private string BuildTweakableRangesJson(object scriptable, object rarity, object level, object module)
        {
            var sb = new StringBuilder();
            sb.Append("[");
            if (scriptable == null || rarity == null) { sb.Append("]"); return sb.ToString(); }
            try
            {
                MethodInfo getTweakables = null;
                foreach (var gm in scriptable.GetType().GetMethods(BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Instance))
                {
                    if (gm.Name == "GetTweakableValuesForRarity" && gm.GetParameters().Length == 1) { getTweakables = gm; break; }
                }
                object list = getTweakables?.Invoke(scriptable, new object[] { rarity });
                if (list == null) { sb.Append("]"); return sb.ToString(); }

                int upgradeLevel = SafeInt(level);
                float[] rolls = module != null ? ReadFloatArray(GetInstanceMemberValue(module, "m_BaseValueRolls")) : new float[0];
                bool first = true;
                int twIndex = 0;
                foreach (var tw in ReadIndexedCollection(list))
                {
                    int thisIndex = twIndex++;
                    if (tw == null) continue;
                    MethodInfo calc = null;
                    foreach (var cm in tw.GetType().GetMethods(BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Instance))
                    {
                        if (cm.Name == "CalculateRolledValue" && cm.GetParameters().Length == 2) { calc = cm; break; }
                    }
                    if (calc == null) continue;

                    string twName = GetInstanceMemberValue(tw, "m_Name") as string;
                    float low, high;
                    try
                    {
                        object atMin = calc.Invoke(tw, new object[] { 0f, upgradeLevel });
                        object atMax = calc.Invoke(tw, new object[] { 1f, upgradeLevel });
                        float a = atMin is float fa ? fa : 0f;
                        float b = atMax is float fb ? fb : 0f;
                        low = Math.Min(a, b);
                        high = Math.Max(a, b);
                    }
                    catch { continue; }

                    float currentRoll = thisIndex < rolls.Length ? rolls[thisIndex] : 0f;
                    float currentValue = low;
                    try
                    {
                        object atCurrent = calc.Invoke(tw, new object[] { currentRoll, upgradeLevel });
                        if (atCurrent is float fc) currentValue = fc;
                    }
                    catch { }

                    if (!first) sb.Append(",");
                    first = false;
                    sb.Append("{\"name\":").Append(JsonStr(twName))
                      .Append(",\"index\":").Append(thisIndex)
                      .Append(",\"low\":").Append(low.ToString(System.Globalization.CultureInfo.InvariantCulture))
                      .Append(",\"high\":").Append(high.ToString(System.Globalization.CultureInfo.InvariantCulture))
                      .Append(",\"roll\":").Append(currentRoll.ToString(System.Globalization.CultureInfo.InvariantCulture))
                      .Append(",\"current\":").Append(currentValue.ToString(System.Globalization.CultureInfo.InvariantCulture))
                      .Append("}");
                }
            }
            catch (Exception ex) { Log("BuildTweakableRangesJson threw: " + ex.Message); }
            sb.Append("]");
            return sb.ToString();
        }

        // Writes a single tweakable's roll (0-1, clamped) directly into a
        // module's m_BaseValueRolls[tweakableIndex] - same array Reroll
        // already populates, just targeting one slot instead of rebuilding
        // the whole array. Returns the new array length on success (-1 on
        // failure) so callers can validate tweakableIndex was in range.
        // Cheat Mode ceiling for a roll - a real roll is statistically 0-1,
        // but pushing it past 1.0 just linearly extrapolates past a
        // module's normal max stat value in CalculateRolledValue (confirmed
        // safe to feed it an out-of-range float - see GetSingleTweakableCurrentValue).
        // 3.0 (300%) is a generous but finite cheat headroom, not unbounded,
        // to keep the numbers sane rather than feeding something absurd into
        // the game's own stat formula.
        private const float CheatModeRollCeiling = 3f;

        private bool SetModuleRollValue(object module, int tweakableIndex, float roll)
        {
            if (module == null || tweakableIndex < 0) return false;
            float ceiling = _cheatModeEnabled ? CheatModeRollCeiling : 1f;
            roll = Math.Max(0f, Math.Min(ceiling, roll));
            try
            {
                var rollsProp = module.GetType().GetProperty("m_BaseValueRolls", BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Instance);
                if (rollsProp == null) { Log("SetModuleRollValue: m_BaseValueRolls property not found."); return false; }
                object rollsArray = rollsProp.GetValue(module);
                if (rollsArray == null) { Log("SetModuleRollValue: m_BaseValueRolls is null."); return false; }
                var itemProp = rollsArray.GetType().GetProperty("Item", BindingFlags.Public | BindingFlags.Instance);
                if (itemProp == null) { Log("SetModuleRollValue: m_BaseValueRolls has no Item indexer."); return false; }
                int length = 0;
                var lengthProp = rollsArray.GetType().GetProperty("Length", BindingFlags.Public | BindingFlags.Instance);
                if (lengthProp != null) length = SafeInt(lengthProp.GetValue(rollsArray));
                if (tweakableIndex >= length) { Log($"SetModuleRollValue: tweakableIndex {tweakableIndex} out of range (length {length})."); return false; }
                itemProp.SetValue(rollsArray, roll, new object[] { tweakableIndex });
                return true;
            }
            catch (Exception ex) { Log("SetModuleRollValue threw: " + ex.Message); return false; }
        }

        // Re-derives just one tweakable's current displayed value (module's
        // own stored roll at tweakableIndex, run through the official
        // CalculateRolledValue) - used after SetModuleRollValue so the HTTP
        // response can hand back the authoritative recomputed number instead
        // of making the caller re-fetch the whole card.
        private float GetSingleTweakableCurrentValue(object scriptable, object rarity, object level, object module, int tweakableIndex)
        {
            if (scriptable == null || rarity == null || module == null) return 0f;
            try
            {
                MethodInfo getTweakables = null;
                foreach (var gm in scriptable.GetType().GetMethods(BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Instance))
                {
                    if (gm.Name == "GetTweakableValuesForRarity" && gm.GetParameters().Length == 1) { getTweakables = gm; break; }
                }
                object list = getTweakables?.Invoke(scriptable, new object[] { rarity });
                if (list == null) return 0f;
                var entries = ReadIndexedCollection(list);
                if (tweakableIndex < 0 || tweakableIndex >= entries.Count) return 0f;
                object tw = entries[tweakableIndex];
                if (tw == null) return 0f;

                MethodInfo calc = null;
                foreach (var cm in tw.GetType().GetMethods(BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Instance))
                {
                    if (cm.Name == "CalculateRolledValue" && cm.GetParameters().Length == 2) { calc = cm; break; }
                }
                if (calc == null) return 0f;

                float[] rolls = ReadFloatArray(GetInstanceMemberValue(module, "m_BaseValueRolls"));
                float roll = tweakableIndex < rolls.Length ? rolls[tweakableIndex] : 0f;
                int upgradeLevel = SafeInt(level);
                object result = calc.Invoke(tw, new object[] { roll, upgradeLevel });
                return result is float f ? f : 0f;
            }
            catch (Exception ex) { Log("GetSingleTweakableCurrentValue threw: " + ex.Message); return 0f; }
        }

        // The game's descriptions come formatted with Unity rich-text markup
        // for TextMeshPro (<b>, <color=#RRGGBB>, <size=...>, etc.), which just
        // shows up as literal text in a plain HTML dropdown/description. Strips
        // any <...> tag rather than trying to allowlist specific ones, since
        // the game can use whatever tags it wants here.
        private static string StripRichText(string s)
        {
            if (string.IsNullOrEmpty(s)) return s;
            try { return Regex.Replace(s, "<.*?>", ""); }
            catch { return s; }
        }

        private string BuildCurrenciesJson()
        {
            var getMethod = _mgrType.GetMethod("GetCurrency", BindingFlags.Public | BindingFlags.Static);
            var creditsCurrencyProp = _mgrType.GetProperty("CreditsCurrency", BindingFlags.Public | BindingFlags.Static);

            int creditsAmount = 0;
            if (creditsCurrencyProp != null && getMethod != null)
            {
                try { creditsAmount = (int)getMethod.Invoke(null, new object[] { creditsCurrencyProp.GetValue(null) }); } catch { }
            }

            var ingots = GetIngotCurrencies();
            var ingotAmounts = new List<int>();
            for (int i = 0; i < ingots.Count; i++)
            {
                int amt = 0;
                if (getMethod != null) { try { amt = (int)getMethod.Invoke(null, new object[] { ingots[i] }); } catch { } }
                ingotAmounts.Add(amt);
            }
            EnsureCurrencySnapshot(creditsAmount, ingotAmounts);

            var sb = new StringBuilder();
            sb.Append("{\"credits\":").Append(creditsAmount).Append(",\"ingots\":[");
            for (int i = 0; i < ingots.Count; i++)
            {
                if (i > 0) sb.Append(",");
                string name = IngotDisplayName(i, ingots[i]);
                sb.Append("{\"index\":").Append(i).Append(",\"name\":").Append(JsonStr(name)).Append(",\"amount\":").Append(ingotAmounts[i]).Append("}");
            }
            sb.Append("]}");
            return sb.ToString();
        }

        // No scene/hangar concept anymore - Jump Space keeps everything in one
        // persistent Unity scene ('Session'/'Global'), so there was never a
        // real signal there.
        //
        // Blueprint count alone turned out not to be quite enough either: at
        // the main menu, the blueprint list can still read back non-empty
        // (MetaProgressionManager is a persistent singleton, so it likely
        // holds onto the LAST loaded save's blueprints rather than clearing
        // them on return to menu) while currencies genuinely reset to 0 -
        // which is exactly the "shows currencies as 0 at the main menu"
        // report. Requiring at least one currency to be non-zero too catches
        // that mismatch, at the cost of also hiding the panel for a
        // genuinely-broke-in-hangar player (rare edge case, acceptable
        // trade-off here).
        private string BuildGameStateJson()
        {
            int blueprintCount = GetBlueprintsSnapshot().Count;
            bool currenciesLookReal = CurrenciesLookReal();
            bool dataLoaded = blueprintCount > 0 && currenciesLookReal;
            return "{\"dataLoaded\":" + (dataLoaded ? "true" : "false")
                 + ",\"blueprintCount\":" + blueprintCount
                 + ",\"currenciesLookReal\":" + (currenciesLookReal ? "true" : "false") + "}";
        }

        private bool CurrenciesLookReal()
        {
            try
            {
                var getMethod = _mgrType.GetMethod("GetCurrency", BindingFlags.Public | BindingFlags.Static);
                if (getMethod == null) return false;

                var creditsCurrencyProp = _mgrType.GetProperty("CreditsCurrency", BindingFlags.Public | BindingFlags.Static);
                object credits = creditsCurrencyProp?.GetValue(null);
                if (credits != null)
                {
                    try { if ((int)getMethod.Invoke(null, new object[] { credits }) > 0) return true; } catch { }
                }
                foreach (var ingot in GetIngotCurrencies())
                {
                    try { if ((int)getMethod.Invoke(null, new object[] { ingot }) > 0) return true; } catch { }
                }
            }
            catch (Exception ex) { Log("CurrenciesLookReal threw: " + ex.Message); }
            return false;
        }

        private string BuildModuleTypesJson()
        {
            if (_moduleCandidates.Count == 0) RefreshModuleCandidates(false);
            var sb = new StringBuilder();
            sb.Append("[");
            for (int i = 0; i < _moduleCandidates.Count; i++)
            {
                if (i > 0) sb.Append(",");
                var c = _moduleCandidates[i];
                // Representative description for the dropdown: uses this
                // module's own min rarity + level 0 (no specific instance to
                // roll values from at this point, since this is the generic
                // type list, not a slot) - same GetLocalizedDescription call
                // TryGetModuleDescription already uses elsewhere, so it'll show
                // real in-game text (e.g. "+{0:0%} Damage" resolved with
                // placeholder values) rather than nothing.
                object minRarityValue = GetInstanceMemberValue(c.Scriptable, "m_MinRarity");
                string desc = TryGetModuleDescription(c.Scriptable, minRarityValue, 0, null);
                sb.Append("{\"index\":").Append(i)
                  .Append(",\"name\":").Append(JsonStr(c.DisplayName))
                  .Append(",\"guid\":").Append(JsonStr(c.Guid))
                  .Append(",\"rarity\":").Append(JsonStr(GetRarityRangeString(c.Scriptable)))
                  .Append(",\"description\":").Append(JsonStr(desc))
                  .Append(",\"allowed\":").Append(JsonStrArray(c.AllowedTemplateGuids))
                  .Append(",\"forbidden\":").Append(JsonStrArray(c.ForbiddenTemplateGuids))
                  .Append(",\"isBasic\":").Append(c.IsBasicModule ? "true" : "false")
                  .Append("}");
            }
            sb.Append("]");
            return sb.ToString();
        }

        private string BuildCosmeticTypesJson()
        {
            if (_cosmeticCandidates.Count == 0) RefreshCosmeticCandidates();
            var sb = new StringBuilder();
            sb.Append("[");
            for (int i = 0; i < _cosmeticCandidates.Count; i++)
            {
                if (i > 0) sb.Append(",");
                var c = _cosmeticCandidates[i];
                sb.Append("{\"index\":").Append(i)
                  .Append(",\"name\":").Append(JsonStr(c.DisplayName))
                  .Append(",\"guid\":").Append(JsonStr(c.Guid))
                  .Append(",\"slotType\":").Append(JsonStr(c.SlotType))
                  .Append(",\"isAttachment\":").Append(c.IsAttachment ? "true" : "false")
                  .Append("}");
            }
            sb.Append("]");
            return sb.ToString();
        }

        private void HandleUpgradeLevel(HttpListenerContext ctx)
        {
            int bpIndex = QueryInt(ctx, "blueprintIndex", -1);
            int modIndex = QueryInt(ctx, "moduleIndex", -1);

            var blueprints = GetBlueprintsSnapshot();
            if (bpIndex < 0 || bpIndex >= blueprints.Count) { WriteJson(ctx, 400, "{\"error\":\"bad blueprintIndex\"}"); return; }
            object bp = blueprints[bpIndex];

            // GUI upgrades shouldn't require you to actually have the
            // resources: snapshot every currency, top them all up so the
            // official upgrade call can never fail on cost, then put every
            // currency back to its exact original amount afterward (whether
            // the upgrade succeeded or not). Net effect: the upgrade is free,
            // your balances end up completely unchanged.
            var currencySnapshot = SnapshotAllCurrencies();
            EnsurePlentyOfAllCurrencies();

            object result = null;
            try
            {
                if (modIndex < 0)
                {
                    var m = _mgrType.GetMethod("TryUpgradeBlueprint", BindingFlags.Public | BindingFlags.Static);
                    if (m != null) result = m.Invoke(null, new object[] { bp });
                }
                else
                {
                    var m = _mgrType.GetMethod("TryModifyBlueprintModuleLevel", BindingFlags.Public | BindingFlags.Static);
                    if (m != null) result = m.Invoke(null, new object[] { bp, modIndex, 1 });
                }
            }
            finally
            {
                RestoreCurrencies(currencySnapshot);
            }

            SaveNow();
            WriteJson(ctx, 200, "{\"ok\":" + (Equals(result, true) ? "true" : "false") + "}");
        }

        // TryUpgradeBlueprint (used by the "Upgrade Level" button above) only
        // ever goes up by 1 and has no matching "downgrade" call - it's the
        // real assembler's official upgrade action, not a general level
        // setter. Same "direct unofficial write" approach HandleInventorySetLevel
        // already uses for carried items: write m_Level straight onto the
        // blueprint's own m_GeneratedData, which supports going up OR down to
        // any value, no resource cost either way.
        private void HandleSetLevel(HttpListenerContext ctx)
        {
            int bpIndex = QueryInt(ctx, "blueprintIndex", -1);
            int level = QueryInt(ctx, "level", -1);
            if (level < 0) { WriteJson(ctx, 400, "{\"error\":\"missing or bad level\"}"); return; }

            var blueprints = GetBlueprintsSnapshot();
            if (bpIndex < 0 || bpIndex >= blueprints.Count) { WriteJson(ctx, 400, "{\"error\":\"bad blueprintIndex\"}"); return; }
            object bp = blueprints[bpIndex];
            object generatedData = GetInstanceMemberValue(bp, "m_GeneratedData");
            bool wrote = TrySetInstanceMemberValue(generatedData, "m_Level", level);
            bool wroteBack = wrote && TrySetInstanceMemberValue(bp, "m_GeneratedData", generatedData);
            Log($"HandleSetLevel: blueprint[{bpIndex}] m_Level <- {level}, wrote={wrote}, wroteBack={wroteBack}.");
            if (wroteBack) SaveNow();
            WriteJson(ctx, 200, "{\"ok\":" + (wroteBack ? "true" : "false") + "}");
        }

        private class CurrencySnapshot
        {
            public object Currency;
            public int Amount;
        }

        private List<CurrencySnapshot> SnapshotAllCurrencies()
        {
            var list = new List<CurrencySnapshot>();
            var getMethod = _mgrType.GetMethod("GetCurrency", BindingFlags.Public | BindingFlags.Static);
            if (getMethod == null) return list;

            var creditsCurrencyProp = _mgrType.GetProperty("CreditsCurrency", BindingFlags.Public | BindingFlags.Static);
            if (creditsCurrencyProp != null)
            {
                object credits = creditsCurrencyProp.GetValue(null);
                if (credits != null)
                {
                    try { list.Add(new CurrencySnapshot { Currency = credits, Amount = (int)getMethod.Invoke(null, new object[] { credits }) }); }
                    catch (Exception ex) { Log("SnapshotAllCurrencies: reading credits failed: " + ex.Message); }
                }
            }
            foreach (var ingot in GetIngotCurrencies())
            {
                try { list.Add(new CurrencySnapshot { Currency = ingot, Amount = (int)getMethod.Invoke(null, new object[] { ingot }) }); }
                catch (Exception ex) { Log("SnapshotAllCurrencies: reading an ingot failed: " + ex.Message); }
            }
            return list;
        }

        private void EnsurePlentyOfAllCurrencies()
        {
            const int plenty = 999999999;
            var setCurrencyMethod = _mgrType.GetMethod("SetCurrency", BindingFlags.Public | BindingFlags.Static);
            if (setCurrencyMethod == null) { Log("EnsurePlentyOfAllCurrencies: SetCurrency not found."); return; }

            var creditsCurrencyProp = _mgrType.GetProperty("CreditsCurrency", BindingFlags.Public | BindingFlags.Static);
            if (creditsCurrencyProp != null)
            {
                object credits = creditsCurrencyProp.GetValue(null);
                if (credits != null) { try { setCurrencyMethod.Invoke(null, new object[] { credits, plenty }); } catch { } }
            }
            foreach (var ingot in GetIngotCurrencies())
            {
                try { setCurrencyMethod.Invoke(null, new object[] { ingot, plenty }); } catch { }
            }
        }

        private void RestoreCurrencies(List<CurrencySnapshot> snapshot)
        {
            var setCurrencyMethod = _mgrType.GetMethod("SetCurrency", BindingFlags.Public | BindingFlags.Static);
            if (setCurrencyMethod == null) return;
            foreach (var s in snapshot)
            {
                try { setCurrencyMethod.Invoke(null, new object[] { s.Currency, s.Amount }); }
                catch (Exception ex) { Log("RestoreCurrencies: could not restore a currency: " + ex.Message); }
            }
        }

        private void HandleSetRarity(HttpListenerContext ctx)
        {
            int bpIndex = QueryInt(ctx, "blueprintIndex", -1);
            int modIndex = QueryInt(ctx, "moduleIndex", -1);
            string rarityName = QueryString(ctx, "rarity", null);

            var blueprints = GetBlueprintsSnapshot();
            if (bpIndex < 0 || bpIndex >= blueprints.Count) { WriteJson(ctx, 400, "{\"error\":\"bad blueprintIndex\"}"); return; }
            object bp = blueprints[bpIndex];
            object generatedData = GetInstanceMemberValue(bp, "m_GeneratedData");
            object target = modIndex < 0 ? generatedData : GetModuleAt(generatedData, modIndex);
            if (target == null) { WriteJson(ctx, 400, "{\"error\":\"bad target\"}"); return; }
            Log($"HandleSetRarity: target type={target.GetType().FullName}, IsValueType={target.GetType().IsValueType}.");

            // Upgradeable Features don't have an independently-settable
            // rarity in the real game - they always match the item's own
            // rarity (no such control exists in the assembler UI). The web
            // UI no longer offers this control for basic modules, but block
            // it server-side too in case of a stale tab/cached page still
            // POSTing here - change the item's own rarity instead, which
            // cascades to every basic module automatically (see
            // ResizeModulesForRarity).
            if (modIndex >= 0)
            {
                string targetGuid = GetInstanceMemberValue(target, "m_ModuleGuid") as string;
                var targetCandidate = FindCandidateByGuid(targetGuid);
                if (targetCandidate != null && targetCandidate.IsBasicModule)
                {
                    WriteJson(ctx, 400, "{\"error\":\"Upgradeable Features rarity always matches the item's own rarity - change the item rarity instead, it'll cascade automatically.\"}");
                    return;
                }

                // Per Cameron: limit rarity changes to the module's own
                // valid range (m_MinRarity-m_MaxRarity, same "range: X-Y"
                // tag already shown in the GUI) - the web UI's dropdown no
                // longer offers anything outside it, but block it
                // server-side too in case of a stale/cached tab still
                // POSTing an out-of-range value here.
                if (!_cheatModeEnabled && targetCandidate != null && rarityName != null && !IsRarityWithinRange(targetCandidate.Scriptable, rarityName))
                {
                    WriteJson(ctx, 400, "{\"error\":\"'" + rarityName + "' is outside this module's valid rarity range (" + GetRarityRangeString(targetCandidate.Scriptable) + ") - the game would likely revert it anyway. Enable Cheat Mode to override this.\"}");
                    return;
                }
            }

            if (_itemRarityType == null) _itemRarityType = FindType("Il2CppKeepsake.GeneratedItems.ItemRarity");
            if (_itemRarityType == null || rarityName == null) { WriteJson(ctx, 400, "{\"error\":\"rarity type or value missing\"}"); return; }

            object nextValue;
            try { nextValue = Enum.Parse(_itemRarityType, rarityName, true); }
            catch { WriteJson(ctx, 400, "{\"error\":\"bad rarity name\"}"); return; }

            var prop = target.GetType().GetProperty("m_Rarity", BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Instance);
            bool wrote = false;
            if (prop != null && prop.CanWrite)
            {
                try { prop.SetValue(target, nextValue); wrote = true; } catch (Exception ex) { Log("HandleSetRarity: property SetValue threw: " + ex.Message); }
            }
            if (!wrote && prop != null)
            {
                var setter = target.GetType().GetMethod("set_m_Rarity", BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Instance);
                if (setter != null) { try { setter.Invoke(target, new object[] { nextValue }); wrote = true; } catch (Exception ex) { Log("HandleSetRarity: set_m_Rarity method Invoke threw: " + ex.Message); } }
                else if (prop != null) Log("HandleSetRarity: property CanWrite=false and no set_m_Rarity method found either.");
            }

            object after = prop?.GetValue(target);
            bool confirmed = after != null && string.Equals(after.ToString(), rarityName, StringComparison.OrdinalIgnoreCase);
            Log($"HandleSetRarity: wrote={wrote}, immediate readback on the SAME object='{after}', confirmed={confirmed}.");
            if (confirmed)
            {
                // GeneratedItem/GeneratedModule are almost certainly C# structs
                // (ItemGenerator's own factory methods return Nullable<GeneratedItem>,
                // and Nullable<T> only applies to value types). That means "target"
                // above is a boxed COPY pulled out of bp.m_GeneratedData (or out of
                // its m_Modules array) - the write we just confirmed only touched
                // that disconnected copy. Write it back into its real container now,
                // before doing anything else, or the mutation never sticks.
                if (modIndex < 0)
                {
                    // Per Cameron: turrets/guns have 2 fixed "upgradeable" slots
                    // (damage/reload/mag size etc.) plus 0-3 "custom" module
                    // slots depending on rarity (Standard=0, Refined=1,
                    // Advanced=2, Superior=3). Add/remove custom slots to match
                    // the new rarity before writing generatedData back, so both
                    // land in the same write.
                    ResizeModulesForRarity(generatedData, rarityName, nextValue, bp);

                    bool wroteBack = TrySetInstanceMemberValue(bp, "m_GeneratedData", generatedData);
                    Log($"HandleSetRarity write-back: bp.m_GeneratedData <- mutated copy, wroteBack={wroteBack}.");
                }
                else
                {
                    bool wroteModuleBack = TryWriteModuleBack(generatedData, modIndex, target);
                    bool wroteGeneratedBack = TrySetInstanceMemberValue(bp, "m_GeneratedData", generatedData);
                    Log($"HandleSetRarity write-back: m_Modules[{modIndex}] wroteBack={wroteModuleBack}, bp.m_GeneratedData wroteBack={wroteGeneratedBack}.");
                }

                // Diagnostic (part 1): check BEFORE SaveNow(), to isolate
                // whether saving itself triggers the object-graph rebuild, or
                // whether something else is doing it independently of save.
                {
                    var preSaveBlueprints = GetBlueprintsSnapshot();
                    if (bpIndex < preSaveBlueprints.Count)
                    {
                        object preBp = preSaveBlueprints[bpIndex];
                        object preGenerated = GetInstanceMemberValue(preBp, "m_GeneratedData");
                        object preTarget = modIndex < 0 ? preGenerated : GetModuleAt(preGenerated, modIndex);
                        object preValue = preTarget == null ? null :
                            preTarget.GetType().GetProperty("m_Rarity", BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Instance)?.GetValue(preTarget);
                        bool sameObjectPreSave = ReferenceEquals(target, preTarget);
                        Log($"HandleSetRarity diagnostic (BEFORE SaveNow): wrote '{rarityName}', fresh-fetch readback='{preValue}', same object instance={sameObjectPreSave}.");
                    }
                }

                SaveNow();

                // Diagnostic (part 2): same check again, AFTER SaveNow(), for "it goes back to the original" reports:
                // re-fetch a COMPLETELY FRESH blueprint snapshot (not the same
                // object reference we just wrote to) right after saving, and
                // re-read the same field. If the value comes back wrong here,
                // OR if it's not even the same object instance anymore, that
                // tells us SaveNow()/the save round-trip is what's discarding
                // the edit (e.g. m_UserData getting replaced with a freshly
                // reloaded object graph), not a game-side revert happening
                // later on its own.
                var freshBlueprints = GetBlueprintsSnapshot();
                if (bpIndex < freshBlueprints.Count)
                {
                    object freshBp = freshBlueprints[bpIndex];
                    object freshGenerated = GetInstanceMemberValue(freshBp, "m_GeneratedData");
                    object freshTarget = modIndex < 0 ? freshGenerated : GetModuleAt(freshGenerated, modIndex);
                    object freshValue = freshTarget == null ? null :
                        freshTarget.GetType().GetProperty("m_Rarity", BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Instance)?.GetValue(freshTarget);
                    bool sameObject = ReferenceEquals(target, freshTarget);
                    Log($"HandleSetRarity diagnostic: wrote '{rarityName}', immediate readback='{after}', post-SaveNow fresh-fetch readback='{freshValue}', same object instance as before save={sameObject}.");
                }
            }
            WriteJson(ctx, 200, "{\"ok\":" + (confirmed ? "true" : "false") + ",\"value\":" + JsonStr(after == null ? null : after.ToString()) + "}");
        }

        private void HandleSetCurrency(HttpListenerContext ctx)
        {
            // Server-side backstop for hiding currency editing until real save
            // data is loaded - the UI already hides the panel, but this covers
            // a stale tab / cached page still POSTing to this endpoint.
            if (GetBlueprintsSnapshot().Count == 0)
            {
                WriteJson(ctx, 403, "{\"error\":\"Currency editing isn't available yet - blueprint data hasn't loaded.\"}");
                return;
            }

            string which = QueryString(ctx, "which", "");
            int amount = QueryInt(ctx, "amount", 0);
            var setCurrencyMethod = _mgrType.GetMethod("SetCurrency", BindingFlags.Public | BindingFlags.Static);
            if (setCurrencyMethod == null) { WriteJson(ctx, 500, "{\"error\":\"SetCurrency not found\"}"); return; }

            object currency;
            if (which == "credits")
            {
                var prop = _mgrType.GetProperty("CreditsCurrency", BindingFlags.Public | BindingFlags.Static);
                currency = prop?.GetValue(null);
            }
            else
            {
                int idx = QueryInt(ctx, "index", -1);
                var ingots = GetIngotCurrencies();
                currency = (idx >= 0 && idx < ingots.Count) ? ingots[idx] : null;
            }
            if (currency == null) { WriteJson(ctx, 400, "{\"error\":\"unknown currency\"}"); return; }

            try { setCurrencyMethod.Invoke(null, new object[] { currency, amount }); }
            catch (Exception ex) { WriteJson(ctx, 500, "{\"error\":" + JsonStr(ex.Message) + "}"); return; }

            WriteJson(ctx, 200, "{\"ok\":true}");
        }

        private void HandleSwapModule(HttpListenerContext ctx)
        {
            int bpIndex = QueryInt(ctx, "blueprintIndex", -1);
            int modIndex = QueryInt(ctx, "moduleIndex", -1);
            string guid = QueryString(ctx, "moduleGuid", null);

            if (guid == null) { WriteJson(ctx, 400, "{\"error\":\"missing moduleGuid\"}"); return; }
            if (_moduleCandidates.Count == 0) RefreshModuleCandidates(false);

            ModuleCandidate candidate = null;
            foreach (var c in _moduleCandidates) { if (c.Guid == guid) { candidate = c; break; } }
            if (candidate == null) { WriteJson(ctx, 400, "{\"error\":\"unknown moduleGuid\"}"); return; }

            var blueprints = GetBlueprintsSnapshot();
            if (bpIndex < 0 || bpIndex >= blueprints.Count) { WriteJson(ctx, 400, "{\"error\":\"bad blueprintIndex\"}"); return; }
            object bp = blueprints[bpIndex];
            object generatedData = GetInstanceMemberValue(bp, "m_GeneratedData");
            object module = GetModuleAt(generatedData, modIndex);
            if (module == null) { WriteJson(ctx, 400, "{\"error\":\"bad moduleIndex\"}"); return; }
            Log($"HandleSwapModule: module type={module.GetType().FullName}, IsValueType={module.GetType().IsValueType}.");

            var guidProp = module.GetType().GetProperty("m_ModuleGuid", BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Instance);
            if (guidProp == null) { WriteJson(ctx, 500, "{\"error\":\"m_ModuleGuid not found\"}"); return; }

            bool wroteGuid = false;
            if (guidProp.CanWrite)
            {
                try { guidProp.SetValue(module, candidate.Guid); wroteGuid = true; } catch (Exception ex) { Log("HandleSwapModule: guid property SetValue threw: " + ex.Message); }
            }
            if (wroteGuid)
            {
                // Same struct-copy concern as rarity: CanWrite can be true and
                // SetValue can succeed without throwing, yet not actually stick
                // if "module" is a boxed copy of a value type. Confirm by
                // reading back from the SAME object before trusting it.
                object check = guidProp.GetValue(module);
                if (!(check is string s) || s != candidate.Guid) wroteGuid = false;
            }
            if (!wroteGuid)
            {
                var setter = module.GetType().GetMethod("set_m_ModuleGuid", BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Instance);
                if (setter != null)
                {
                    try { setter.Invoke(module, new object[] { candidate.Guid }); } catch (Exception ex) { Log("HandleSwapModule: set_m_ModuleGuid method Invoke threw: " + ex.Message); }
                    object check = guidProp.GetValue(module);
                    wroteGuid = check is string s2 && s2 == candidate.Guid;
                }
                else
                {
                    Log("HandleSwapModule: guid property CanWrite=false and no set_m_ModuleGuid method found either.");
                }
            }
            Log($"HandleSwapModule: wroteGuid={wroteGuid} (immediate readback on the SAME object).");
            if (!wroteGuid)
            {
                WriteJson(ctx, 500, "{\"error\":\"could not write m_ModuleGuid (read-only or interop write didn't stick)\"}");
                return;
            }

            try
            {
                object rarityObj = GetInstanceMemberValue(module, "m_Rarity");
                var getTweakables = candidate.Scriptable.GetType().GetMethod("GetTweakableValuesForRarity", BindingFlags.Public | BindingFlags.Instance);
                int rollCount = 1;
                if (getTweakables != null && rarityObj != null)
                {
                    object list = getTweakables.Invoke(candidate.Scriptable, new object[] { rarityObj });
                    var countProp = list == null ? null : list.GetType().GetProperty("Count", BindingFlags.Public | BindingFlags.Instance);
                    if (countProp != null) rollCount = Math.Max(1, (int)countProp.GetValue(list));
                }

                var rollsProp = module.GetType().GetProperty("m_BaseValueRolls", BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Instance);
                if (rollsProp != null)
                {
                    var arrayType = rollsProp.PropertyType;
                    object newArray = Activator.CreateInstance(arrayType, new object[] { rollCount });
                    var itemProp = arrayType.GetProperty("Item", BindingFlags.Public | BindingFlags.Instance);
                    if (itemProp != null)
                    {
                        for (int i = 0; i < rollCount; i++)
                            itemProp.SetValue(newArray, 0.5f, new object[] { i });
                    }
                    rollsProp.SetValue(module, newArray);
                }
            }
            catch (Exception ex) { Log("HandleSwapModule: m_BaseValueRolls rebuild threw: " + ex.Message); }

            // GeneratedModule is almost certainly a C# struct (see the comment
            // above HandleSetRarity for why) - "module" above is a boxed COPY
            // pulled out of m_Modules[modIndex]. Everything we just wrote
            // (guid + rolls) only touched that disconnected copy so far; write
            // it back into the real array now, or none of it sticks.
            {
                bool wroteModuleBack = TryWriteModuleBack(generatedData, modIndex, module);
                bool wroteGeneratedBack = TrySetInstanceMemberValue(bp, "m_GeneratedData", generatedData);
                Log($"HandleSwapModule write-back: m_Modules[{modIndex}] wroteBack={wroteModuleBack}, bp.m_GeneratedData wroteBack={wroteGeneratedBack}.");
            }

            // Diagnostic (part 1): check BEFORE calling SaveNow(), to isolate
            // whether the save call itself triggers a rebuild of the live
            // object graph, or whether something else (e.g. a periodic
            // network/reconciliation tick) is doing it independently of save.
            {
                var preSaveBlueprints = GetBlueprintsSnapshot();
                if (bpIndex < preSaveBlueprints.Count)
                {
                    object preBp = preSaveBlueprints[bpIndex];
                    object preGenerated = GetInstanceMemberValue(preBp, "m_GeneratedData");
                    object preModule = GetModuleAt(preGenerated, modIndex);
                    object preGuid = preModule == null ? null : GetInstanceMemberValue(preModule, "m_ModuleGuid");
                    bool sameObjectPreSave = ReferenceEquals(module, preModule);
                    Log($"HandleSwapModule diagnostic (BEFORE SaveNow): wrote guid '{candidate.Guid}', fresh-fetch guid='{preGuid}', same object instance={sameObjectPreSave}.");
                }
            }

            SaveNow();

            // Diagnostic (part 2): same check again, AFTER SaveNow().
            var freshBlueprints2 = GetBlueprintsSnapshot();
            if (bpIndex < freshBlueprints2.Count)
            {
                object freshBp = freshBlueprints2[bpIndex];
                object freshGenerated = GetInstanceMemberValue(freshBp, "m_GeneratedData");
                object freshModule = GetModuleAt(freshGenerated, modIndex);
                object freshGuid = freshModule == null ? null : GetInstanceMemberValue(freshModule, "m_ModuleGuid");
                bool sameObject = ReferenceEquals(module, freshModule);
                Log($"HandleSwapModule diagnostic (AFTER SaveNow): wrote guid '{candidate.Guid}', fresh-fetch guid='{freshGuid}', same object instance={sameObject}.");
            }

            WriteJson(ctx, 200, "{\"ok\":true,\"name\":" + JsonStr(candidate.DisplayName) + "}");
        }

        // Swaps which cosmetic (scope, color, etc.) is plugged into one
        // CosmeticSelection slot on an item - e.g. changing an on-foot gun's
        // scope. Same write-back pattern as HandleSwapModule: CosmeticSelection
        // reads as IsValueType=False under reflection but still needs to be
        // written back into its array (and generatedData back into the
        // blueprint) or the mutation never sticks.
        private void HandleSwapCosmetic(HttpListenerContext ctx)
        {
            int bpIndex = QueryInt(ctx, "blueprintIndex", -1);
            int cosmeticIndex = QueryInt(ctx, "cosmeticIndex", -1);
            string cosmeticGuid = QueryString(ctx, "cosmeticGuid", null);

            if (cosmeticGuid == null) { WriteJson(ctx, 400, "{\"error\":\"missing cosmeticGuid\"}"); return; }
            if (_cosmeticCandidates.Count == 0) RefreshCosmeticCandidates();

            CosmeticCandidate candidate = null;
            foreach (var c in _cosmeticCandidates) { if (c.Guid == cosmeticGuid) { candidate = c; break; } }
            if (candidate == null) { WriteJson(ctx, 400, "{\"error\":\"unknown cosmeticGuid\"}"); return; }

            var blueprints = GetBlueprintsSnapshot();
            if (bpIndex < 0 || bpIndex >= blueprints.Count) { WriteJson(ctx, 400, "{\"error\":\"bad blueprintIndex\"}"); return; }
            object bp = blueprints[bpIndex];
            object generatedData = GetInstanceMemberValue(bp, "m_GeneratedData");
            object cosmetic = GetCosmeticAt(generatedData, cosmeticIndex);
            if (cosmetic == null) { WriteJson(ctx, 400, "{\"error\":\"bad cosmeticIndex\"}"); return; }

            // Sanity check: only let a slot take a cosmetic of the SAME slot
            // type it already has (e.g. don't let a Scope slot accept a Color
            // cosmetic) - the game almost certainly enforces this itself, but
            // there's no reason to test that the hard way.
            object existingSlotType = GetInstanceMemberValue(cosmetic, "m_SlotType");
            string existingSlotTypeName = existingSlotType?.ToString();
            if (!string.IsNullOrEmpty(existingSlotTypeName) && !string.IsNullOrEmpty(candidate.SlotType)
                && !string.Equals(existingSlotTypeName, candidate.SlotType, StringComparison.OrdinalIgnoreCase))
            {
                WriteJson(ctx, 400, "{\"error\":\"slot type mismatch: this slot is '" + existingSlotTypeName + "', that cosmetic is '" + candidate.SlotType + "'\"}");
                return;
            }

            bool wroteGuid = TrySetInstanceMemberValue(cosmetic, "m_CosmeticGuid", candidate.Guid);
            if (wroteGuid)
            {
                object check = GetInstanceMemberValue(cosmetic, "m_CosmeticGuid");
                wroteGuid = (check as string) == candidate.Guid;
            }
            Log($"HandleSwapCosmetic: blueprint[{bpIndex}] cosmetic[{cosmeticIndex}] wroteGuid={wroteGuid} (immediate readback on the SAME object).");
            if (!wroteGuid) { WriteJson(ctx, 500, "{\"error\":\"could not write m_CosmeticGuid (read-only or interop write didn't stick)\"}"); return; }

            bool wroteCosmeticBack = TryWriteCosmeticBack(generatedData, cosmeticIndex, cosmetic);
            bool wroteGeneratedBack = TrySetInstanceMemberValue(bp, "m_GeneratedData", generatedData);
            Log($"HandleSwapCosmetic write-back: m_Cosmetics[{cosmeticIndex}] wroteBack={wroteCosmeticBack}, bp.m_GeneratedData wroteBack={wroteGeneratedBack}.");

            if (wroteCosmeticBack) SaveNow();
            WriteJson(ctx, 200, "{\"ok\":" + (wroteCosmeticBack ? "true" : "false") + ",\"name\":" + JsonStr(candidate.DisplayName) + "}");
        }

        private bool ApplyCosmeticSnapshot(object generatedData, int cosmeticIndex, CosmeticSnapshot snap)
        {
            object cosmetic = GetCosmeticAt(generatedData, cosmeticIndex);
            if (cosmetic == null || snap == null || snap.CosmeticGuid == null) return false;
            bool ok = TrySetInstanceMemberValue(cosmetic, "m_CosmeticGuid", snap.CosmeticGuid);
            bool wroteBack = TryWriteCosmeticBack(generatedData, cosmeticIndex, cosmetic);
            return ok && wroteBack;
        }

        private void HandleResetCosmetic(HttpListenerContext ctx)
        {
            int bpIndex = QueryInt(ctx, "blueprintIndex", -1);
            int cosmeticIndex = QueryInt(ctx, "cosmeticIndex", -1);

            var blueprints = GetBlueprintsSnapshot();
            if (bpIndex < 0 || bpIndex >= blueprints.Count) { WriteJson(ctx, 400, "{\"error\":\"bad blueprintIndex\"}"); return; }
            object bp = blueprints[bpIndex];
            object generatedData = GetInstanceMemberValue(bp, "m_GeneratedData");
            string bpGuid = GetInstanceMemberValue(bp, "m_Guid") as string;

            string key = CosmeticSnapshotKey(bpGuid, cosmeticIndex);
            if (!_originalCosmeticSnapshots.TryGetValue(key, out var snap))
            {
                WriteJson(ctx, 400, "{\"error\":\"no original value captured for this cosmetic slot yet - open/refresh the blueprint list once before editing it\"}");
                return;
            }

            bool ok = ApplyCosmeticSnapshot(generatedData, cosmeticIndex, snap);
            bool wroteGeneratedBack = TrySetInstanceMemberValue(bp, "m_GeneratedData", generatedData);
            Log($"HandleResetCosmetic: blueprint[{bpIndex}] cosmetic[{cosmeticIndex}] reset to original, applySnapshot={ok}, bp.m_GeneratedData wroteBack={wroteGeneratedBack}.");
            if (ok) SaveNow();
            WriteJson(ctx, 200, "{\"ok\":" + (ok ? "true" : "false") + "}");
        }

        // Changes what item this blueprint fundamentally IS (e.g. Sideclip ->
        // Scorpion), not just its rarity/level/modules. Mechanically this is
        // the exact same write-back pattern as HandleSwapModule (GeneratedItem
        // reads as IsValueType=False under reflection but still needs its
        // container written back, same as GeneratedModule/GeneratedItem
        // rarity writes elsewhere) - we deliberately do NOT call
        // ItemGenerator.Generate/GenerateForTemplate here even though a real
        // one exists (confirmed via "Dump ItemGenerator"): both take a
        // Random/IList/Func-delegate parameter set that's fragile to marshal
        // through Il2Cpp reflection, versus this low-level field write which
        // mirrors code that's already proven reliable.
        private void HandleChangeItemTemplate(HttpListenerContext ctx)
        {
            int bpIndex = QueryInt(ctx, "blueprintIndex", -1);
            string newTemplateGuid = QueryString(ctx, "templateGuid", null);
            if (string.IsNullOrEmpty(newTemplateGuid)) { WriteJson(ctx, 400, "{\"error\":\"missing templateGuid\"}"); return; }

            var blueprints = GetBlueprintsSnapshot();
            if (bpIndex < 0 || bpIndex >= blueprints.Count) { WriteJson(ctx, 400, "{\"error\":\"bad blueprintIndex\"}"); return; }
            object bp = blueprints[bpIndex];
            object generatedData = GetInstanceMemberValue(bp, "m_GeneratedData");
            if (generatedData == null) { WriteJson(ctx, 400, "{\"error\":\"no generatedData on this blueprint\"}"); return; }

            string oldTemplateGuid = GetInstanceMemberValue(generatedData, "m_TemplateGuid") as string;
            Log($"HandleChangeItemTemplate: blueprint[{bpIndex}] templateGuid '{oldTemplateGuid}' -> '{newTemplateGuid}'.");

            bool wroteGuid = TrySetInstanceMemberValue(generatedData, "m_TemplateGuid", newTemplateGuid);
            if (wroteGuid)
            {
                object check = GetInstanceMemberValue(generatedData, "m_TemplateGuid");
                wroteGuid = (check as string) == newTemplateGuid;
            }
            Log($"HandleChangeItemTemplate: wroteGuid={wroteGuid} (immediate readback on the SAME object).");
            if (!wroteGuid) { WriteJson(ctx, 500, "{\"error\":\"could not write m_TemplateGuid (read-only or interop write didn't stick)\"}"); return; }

            // Every module currently equipped was picked/validated against the
            // OLD template's allow/deny lists - none of that carries over, so
            // rebuild every slot against the new template rather than leaving
            // potentially-incompatible modules in place.
            RebuildModulesForNewTemplate(generatedData, newTemplateGuid);

            bool wroteGeneratedBack = TrySetInstanceMemberValue(bp, "m_GeneratedData", generatedData);
            Log($"HandleChangeItemTemplate write-back: bp.m_GeneratedData wroteBack={wroteGeneratedBack}.");

            if (wroteGeneratedBack) SaveNow();
            WriteJson(ctx, 200, "{\"ok\":" + (wroteGeneratedBack ? "true" : "false") + "}");
        }

        // ---------- Duplicate / Delete blueprint ----------
        //
        // Both of these are a genuinely new KIND of operation for this mod -
        // every other feature here only ever modifies an object that already
        // exists in your save data. Duplicate has to fabricate a brand-new,
        // fully independent blueprint entry (its own module/cosmetic arrays,
        // not just copied references to the original's), and Delete has to
        // remove an entry from the raw m_Blueprints list entirely - neither
        // is reflection territory this mod has needed before now. Built the
        // same way every other risky feature in this file was: best-effort
        // reflection with a Log() call at every step, so a failure is
        // diagnosable from Editor_Log.txt in one pass instead of a second
        // guess.

        // Reflection-invokes the protected object.MemberwiseClone() - a
        // full, independent shallow copy of every field, without needing to
        // find or guess a constructor (IL2CPP interop types often don't have
        // an obvious one). Reference-type fields (arrays, nested objects)
        // are still SHARED with the source after this call - see
        // CloneGeneratedDataForDuplicate for where those get deep-cloned on
        // top of this.
        private static readonly MethodInfo _memberwiseCloneMethod =
            typeof(object).GetMethod("MemberwiseClone", BindingFlags.NonPublic | BindingFlags.Instance);

        private object ShallowClone(object src)
        {
            if (src == null) return null;
            try { return _memberwiseCloneMethod.Invoke(src, null); }
            catch (Exception ex) { Log("ShallowClone threw for " + src.GetType().FullName + ": " + ex.Message); return null; }
        }

        // Deep-clones an array-like container (has Length + a read/write
        // Item indexer - the same shape GetModuleAt/GetCosmeticAt/
        // SetModuleRollValue already rely on) into a brand-new, independent
        // instance of the SAME runtime type, via that type's (int size)
        // constructor - the standard shape for both a plain .NET array and
        // an IL2CPP Il2CppReferenceArray<T>/Il2CppStructArray<T>. Falls back
        // to a Clone() method if no (int) constructor is found. elementCloner
        // lets the caller deep-clone each element too (needed for module/
        // cosmetic objects); pass null to copy elements as-is (fine for
        // primitives, like the float[] roll arrays).
        private object CloneArrayLike(object source, Func<object, object> elementCloner)
        {
            if (source == null) return null;
            var t = source.GetType();
            try
            {
                var lengthProp = t.GetProperty("Length", BindingFlags.Public | BindingFlags.Instance);
                var itemProp = t.GetProperty("Item", BindingFlags.Public | BindingFlags.Instance);
                if (lengthProp == null || itemProp == null) { Log("CloneArrayLike: " + t.FullName + " has no Length/Item - can't clone."); return null; }
                int length = (int)lengthProp.GetValue(source);

                object clone = null;
                var ctor = t.GetConstructor(new[] { typeof(int) });
                if (ctor != null) clone = ctor.Invoke(new object[] { length });
                else
                {
                    var cloneMethod = t.GetMethod("Clone", Type.EmptyTypes);
                    if (cloneMethod != null) clone = cloneMethod.Invoke(source, null);
                }
                if (clone == null) { Log("CloneArrayLike: could not construct a new " + t.FullName + " (no (int) constructor and no Clone() method)."); return null; }

                for (int i = 0; i < length; i++)
                {
                    object element = itemProp.GetValue(source, new object[] { i });
                    object clonedElement = elementCloner != null ? elementCloner(element) : element;
                    itemProp.SetValue(clone, clonedElement, new object[] { i });
                }
                return clone;
            }
            catch (Exception ex) { Log("CloneArrayLike threw for " + t.FullName + ": " + ex.Message); return null; }
        }

        // Clones one module element for a duplicated item: MemberwiseClone
        // gets every scalar field (m_ModuleGuid/m_Rarity/m_UpgradeLevel)
        // copied for free, but m_BaseValueRolls is a float[] reference that
        // MemberwiseClone would otherwise leave SHARED with the source
        // module - moving a roll slider on the duplicate would silently
        // also move it on the original. Deep-clone that one field on top of
        // the shallow clone to fix that (see SetModuleRollValue for the
        // same m_BaseValueRolls shape this relies on).
        private object CloneModuleForDuplicate(object sourceModule)
        {
            object clone = ShallowClone(sourceModule);
            if (clone == null) return null;
            object rolls = GetInstanceMemberValue(sourceModule, "m_BaseValueRolls");
            if (rolls != null)
            {
                object clonedRolls = CloneArrayLike(rolls, null);
                if (clonedRolls != null) TrySetInstanceMemberValue(clone, "m_BaseValueRolls", clonedRolls);
                else Log("CloneModuleForDuplicate: could not deep-clone m_BaseValueRolls - duplicate's rolls may still be linked to the original.");
            }
            return clone;
        }

        // CosmeticSelection only carries m_SlotType/m_SlotIndex/
        // m_CosmeticGuid (no nested mutable containers seen anywhere else in
        // this file) - a plain MemberwiseClone is enough, no extra deep
        // clone needed.
        private object CloneCosmeticForDuplicate(object sourceCosmetic) => ShallowClone(sourceCosmetic);

        private object CloneGeneratedDataForDuplicate(object sourceGeneratedData)
        {
            object clone = ShallowClone(sourceGeneratedData);
            if (clone == null) return null;

            object modules = GetInstanceMemberValue(sourceGeneratedData, "m_Modules");
            object clonedModules = CloneArrayLike(modules, CloneModuleForDuplicate);
            if (clonedModules != null) TrySetInstanceMemberValue(clone, "m_Modules", clonedModules);
            else Log("CloneGeneratedDataForDuplicate: could not deep-clone m_Modules - duplicate's modules may still be linked to the original.");

            object cosmetics = GetInstanceMemberValue(sourceGeneratedData, "m_Cosmetics");
            object clonedCosmetics = CloneArrayLike(cosmetics, CloneCosmeticForDuplicate);
            if (clonedCosmetics != null) TrySetInstanceMemberValue(clone, "m_Cosmetics", clonedCosmetics);
            else Log("CloneGeneratedDataForDuplicate: could not deep-clone m_Cosmetics - duplicate's cosmetics may still be linked to the original.");

            return clone;
        }

        private int GetMaxSlotsForCategory(string categoryGuid)
        {
            foreach (var cap in GetBlueprintSlotCapacities())
            {
                string g = GetInstanceMemberValue(cap, "m_CategoryGuid") as string;
                if (string.Equals(g, categoryGuid, StringComparison.OrdinalIgnoreCase))
                    return SafeInt(GetInstanceMemberValue(cap, "m_MaxSlots"));
            }
            return 0;
        }

        private bool TryAddBlueprintToRawList(object newBp)
        {
            try
            {
                object userData = GetPersistentUserData();
                if (userData == null) { Log("TryAddBlueprintToRawList: GetPersistentUserData() returned null."); return false; }
                object list = GetInstanceMemberValue(userData, "m_Blueprints");
                if (list == null) { Log("TryAddBlueprintToRawList: m_Blueprints is null."); return false; }
                var addMethod = list.GetType().GetMethod("Add", BindingFlags.Public | BindingFlags.Instance);
                if (addMethod == null)
                {
                    Log("TryAddBlueprintToRawList: no public Add(T) method on " + list.GetType().FullName + ". Available methods: " + DescribeMethodNames(list.GetType()));
                    return false;
                }
                addMethod.Invoke(list, new object[] { newBp });
                Log("TryAddBlueprintToRawList: Add() invoked without throwing.");
                return true;
            }
            catch (Exception ex) { Log("TryAddBlueprintToRawList threw: " + ex.Message); return false; }
        }

        // Matches by m_Guid rather than trusting bpIndex to still be the
        // right raw-list index (GetBlueprintsSnapshot's order isn't
        // guaranteed to be the raw list's own order - see the blueprint-
        // ordering discovery notes elsewhere in this file). Falls back to
        // the snapshot index only if the target has no guid at all.
        private bool TryRemoveBlueprintFromRawList(string targetGuid, int fallbackIndex)
        {
            try
            {
                object userData = GetPersistentUserData();
                if (userData == null) { Log("TryRemoveBlueprintFromRawList: GetPersistentUserData() returned null."); return false; }
                object list = GetInstanceMemberValue(userData, "m_Blueprints");
                if (list == null) { Log("TryRemoveBlueprintFromRawList: m_Blueprints is null."); return false; }

                var t = list.GetType();
                var countProp = t.GetProperty("Count", BindingFlags.Public | BindingFlags.Instance);
                var itemProp = t.GetProperty("Item", BindingFlags.Public | BindingFlags.Instance);
                int rawIndex = -1;
                if (countProp != null && itemProp != null && !string.IsNullOrEmpty(targetGuid))
                {
                    int count = (int)countProp.GetValue(list);
                    for (int i = 0; i < count; i++)
                    {
                        object entry = itemProp.GetValue(list, new object[] { i });
                        string g = GetInstanceMemberValue(entry, "m_Guid") as string;
                        if (g == targetGuid) { rawIndex = i; break; }
                    }
                }
                if (rawIndex < 0)
                {
                    rawIndex = fallbackIndex;
                    Log("TryRemoveBlueprintFromRawList: guid match failed, falling back to snapshot index " + fallbackIndex + ".");
                }

                var removeAtMethod = t.GetMethod("RemoveAt", BindingFlags.Public | BindingFlags.Instance);
                if (removeAtMethod == null)
                {
                    Log("TryRemoveBlueprintFromRawList: no public RemoveAt(int) method on " + t.FullName + ". Available methods: " + DescribeMethodNames(t));
                    return false;
                }
                removeAtMethod.Invoke(list, new object[] { rawIndex });
                Log("TryRemoveBlueprintFromRawList: RemoveAt(" + rawIndex + ") invoked without throwing.");
                return true;
            }
            catch (Exception ex) { Log("TryRemoveBlueprintFromRawList threw: " + ex.Message); return false; }
        }

        // Diagnostic helper only - lists every distinct public method name on
        // a type, so a failed Add/RemoveAt lookup logs something immediately
        // actionable (the real method name to try next) instead of just "not
        // found".
        private static string DescribeMethodNames(Type t)
        {
            var seen = new HashSet<string>();
            var sb = new StringBuilder();
            foreach (var m in t.GetMethods(BindingFlags.Public | BindingFlags.Instance))
            {
                if (!seen.Add(m.Name)) continue;
                if (sb.Length > 0) sb.Append(", ");
                sb.Append(m.Name);
            }
            return sb.ToString();
        }

        private void HandleDuplicateBlueprint(HttpListenerContext ctx)
        {
            int bpIndex = QueryInt(ctx, "blueprintIndex", -1);
            var blueprints = GetBlueprintsSnapshot();
            if (bpIndex < 0 || bpIndex >= blueprints.Count) { WriteJson(ctx, 400, "{\"error\":\"bad blueprintIndex\"}"); return; }
            object source = blueprints[bpIndex];

            string categoryGuid = GetInstanceMemberValue(source, "m_CategoryGuid") as string;
            if (string.IsNullOrEmpty(categoryGuid)) { WriteJson(ctx, 400, "{\"error\":\"Source item has no category - can't find an open slot for the duplicate.\"}"); return; }

            var takenSlots = new HashSet<int>();
            foreach (var bp in blueprints)
            {
                string g = GetInstanceMemberValue(bp, "m_CategoryGuid") as string;
                if (string.Equals(g, categoryGuid, StringComparison.OrdinalIgnoreCase))
                    takenSlots.Add(SafeInt(GetInstanceMemberValue(bp, "m_SlotIndex")));
            }
            int maxSlots = GetMaxSlotsForCategory(categoryGuid);
            int newSlot = -1;
            for (int s = 0; s < maxSlots; s++) { if (!takenSlots.Contains(s)) { newSlot = s; break; } }
            if (newSlot < 0) { WriteJson(ctx, 400, "{\"error\":\"No open slot in this item's category (" + takenSlots.Count + "/" + maxSlots + " full) - free one up first.\"}"); return; }

            Log($"HandleDuplicateBlueprint: duplicating blueprint[{bpIndex}] (category {categoryGuid}) into new slot {newSlot}.");

            object clonedBp = ShallowClone(source);
            if (clonedBp == null) { WriteJson(ctx, 500, "{\"error\":\"Could not clone this item - see Editor_Log.txt.\"}"); return; }

            object sourceGenerated = GetInstanceMemberValue(source, "m_GeneratedData");
            object clonedGenerated = CloneGeneratedDataForDuplicate(sourceGenerated);
            if (clonedGenerated == null) { WriteJson(ctx, 500, "{\"error\":\"Could not clone this item's generated data - see Editor_Log.txt.\"}"); return; }

            string newGuid = Guid.NewGuid().ToString("N");
            bool wroteGuid = TrySetInstanceMemberValue(clonedBp, "m_Guid", newGuid);
            bool wroteSlot = TrySetInstanceMemberValue(clonedBp, "m_SlotIndex", newSlot);
            bool wroteGenerated = TrySetInstanceMemberValue(clonedBp, "m_GeneratedData", clonedGenerated);
            Log($"HandleDuplicateBlueprint: wroteGuid={wroteGuid}, wroteSlot={wroteSlot}, wroteGenerated={wroteGenerated}.");
            if (!wroteGuid || !wroteSlot || !wroteGenerated)
            {
                WriteJson(ctx, 500, "{\"error\":\"Could not set the duplicate's guid/slot/data - see Editor_Log.txt.\"}");
                return;
            }

            bool added = TryAddBlueprintToRawList(clonedBp);
            if (!added) { WriteJson(ctx, 500, "{\"error\":\"Cloned the item but could not add it to your save data - see Editor_Log.txt.\"}"); return; }

            SaveNow();
            WriteJson(ctx, 200, "{\"ok\":true,\"slotIndex\":" + newSlot + "}");
        }

        private void HandleDeleteBlueprint(HttpListenerContext ctx)
        {
            int bpIndex = QueryInt(ctx, "blueprintIndex", -1);
            var blueprints = GetBlueprintsSnapshot();
            if (bpIndex < 0 || bpIndex >= blueprints.Count) { WriteJson(ctx, 400, "{\"error\":\"bad blueprintIndex\"}"); return; }
            object target = blueprints[bpIndex];
            string targetGuid = GetInstanceMemberValue(target, "m_Guid") as string;

            Log($"HandleDeleteBlueprint: deleting blueprint[{bpIndex}] (guid {targetGuid}).");

            bool removed = TryRemoveBlueprintFromRawList(targetGuid, bpIndex);
            if (!removed) { WriteJson(ctx, 500, "{\"error\":\"Could not remove this item from your save data - see Editor_Log.txt.\"}"); return; }

            SaveNow();
            WriteJson(ctx, 200, "{\"ok\":true}");
        }

        // ---------- Inventory (loose carried items, separate from blueprints) ----------
        // Same write-back concern as everywhere else in this file (isWrapped=
        // False under reflection but a boxed copy needs writing back into its
        // real container): InventoryItem needs writing back into m_Inventory
        // via TryWriteListItemBack (the List<T> equivalent of
        // TryWriteModuleBack's array Item-setter trick), same as
        // GeneratedItem/GeneratedModule need writing back into their own
        // containers. Module/cosmetic editing bodies below mirror the
        // blueprint versions almost exactly - the actual mutation logic
        // (rarity, module swap/reroll, cosmetic swap) is identical since both
        // operate on the same GeneratedItem type; only the "where do I get
        // the container from, and where does it get written back to" differs.

        private void HandleInventorySetAmount(HttpListenerContext ctx)
        {
            int index = QueryInt(ctx, "index", -1);
            string amountStr = QueryString(ctx, "amount", null);
            if (amountStr == null || !float.TryParse(amountStr, System.Globalization.NumberStyles.Float, System.Globalization.CultureInfo.InvariantCulture, out float amount))
            { WriteJson(ctx, 400, "{\"error\":\"missing or bad amount\"}"); return; }

            var items = GetInventorySnapshot();
            if (index < 0 || index >= items.Count) { WriteJson(ctx, 400, "{\"error\":\"bad index\"}"); return; }
            object item = items[index];
            bool wrote = TrySetInstanceMemberValue(item, "m_ResourceAmount", amount);
            bool wroteBack = wrote && TryWriteInventoryItemBack(index, item);
            Log($"HandleInventorySetAmount: inventory[{index}] m_ResourceAmount <- {amount}, wrote={wrote}, wroteBack={wroteBack}.");
            if (wroteBack) SaveNow();
            WriteJson(ctx, 200, "{\"ok\":" + (wroteBack ? "true" : "false") + "}");
        }

        private void HandleInventorySetAmmo(HttpListenerContext ctx)
        {
            int index = QueryInt(ctx, "index", -1);
            int ammo = QueryInt(ctx, "ammo", -1);
            if (ammo < 0) { WriteJson(ctx, 400, "{\"error\":\"missing or bad ammo\"}"); return; }

            var items = GetInventorySnapshot();
            if (index < 0 || index >= items.Count) { WriteJson(ctx, 400, "{\"error\":\"bad index\"}"); return; }
            object item = items[index];
            bool wrote = TrySetInstanceMemberValue(item, "m_AmmoInMag", ammo);
            bool wroteBack = wrote && TryWriteInventoryItemBack(index, item);
            Log($"HandleInventorySetAmmo: inventory[{index}] m_AmmoInMag <- {ammo}, wrote={wrote}, wroteBack={wroteBack}.");
            if (wroteBack) SaveNow();
            WriteJson(ctx, 200, "{\"ok\":" + (wroteBack ? "true" : "false") + "}");
        }

        // "Change Consumable" - the consumable equivalent of
        // HandleChangeItemTemplate, but far simpler: a consumable has no
        // m_GeneratedData/modules to rebuild, its own m_GUID on the
        // InventoryItem IS its type (see RefreshCraftableNames). Just
        // overwrite m_GUID and write the item back into m_Inventory.
        // Deliberately does NOT touch m_ResourceAmount/m_AmmoInMag - amount
        // editing is its own separate concern everywhere else in this file.
        private void HandleSwapConsumable(HttpListenerContext ctx)
        {
            int index = QueryInt(ctx, "index", -1);
            string newGuid = QueryString(ctx, "guid", null);
            if (string.IsNullOrEmpty(newGuid)) { WriteJson(ctx, 400, "{\"error\":\"missing guid\"}"); return; }

            if (_craftableNamesByGuid.Count == 0) RefreshCraftableNames();
            if (_templateOriginalNames.Count == 0) RefreshTemplateOriginalNames();
            if (!IsSwappableConsumableGuid(newGuid)) { WriteJson(ctx, 400, "{\"error\":\"guid not found in the consumable catalog (or filtered out as a non-consumable craftable)\"}"); return; }

            var items = GetInventorySnapshot();
            if (index < 0 || index >= items.Count) { WriteJson(ctx, 400, "{\"error\":\"bad index\"}"); return; }
            object item = items[index];

            string oldGuid = GetInstanceMemberValue(item, "m_GUID") as string;
            Log($"HandleSwapConsumable: inventory[{index}] m_GUID '{oldGuid}' -> '{newGuid}'.");

            bool wroteGuid = TrySetInstanceMemberValue(item, "m_GUID", newGuid);
            if (wroteGuid)
            {
                string check = GetInstanceMemberValue(item, "m_GUID") as string;
                wroteGuid = check == newGuid;
            }
            Log($"HandleSwapConsumable: wroteGuid={wroteGuid} (immediate readback on the SAME object).");
            if (!wroteGuid) { WriteJson(ctx, 500, "{\"error\":\"could not write m_GUID (read-only or interop write didn't stick)\"}"); return; }

            bool wroteListBack = TryWriteInventoryItemBack(index, item);
            Log($"HandleSwapConsumable write-back: wroteListBack={wroteListBack}.");
            if (wroteListBack) SaveNow();
            WriteJson(ctx, 200, "{\"ok\":" + (wroteListBack ? "true" : "false") + "}");
        }

        // Unlike blueprint level (only +1 via the official TryUpgradeBlueprint,
        // since that needs a real Blueprint to call it on), there's no official
        // upgrade path for a loose carried item at all - this is a direct
        // "unofficial" write to any level, same risk profile as the rarity
        // dropdown already uses everywhere else.
        private void HandleInventorySetLevel(HttpListenerContext ctx)
        {
            int index = QueryInt(ctx, "index", -1);
            int level = QueryInt(ctx, "level", -1);
            if (level < 0) { WriteJson(ctx, 400, "{\"error\":\"missing or bad level\"}"); return; }

            var items = GetInventorySnapshot();
            if (index < 0 || index >= items.Count) { WriteJson(ctx, 400, "{\"error\":\"bad index\"}"); return; }
            object item = items[index];
            object generatedData = GetInstanceMemberValue(item, "m_GeneratedData");

            // Per Cameron: no level editing on a weapon while it's carried in
            // inventory - unlike blueprints there's no BlueprintIsUpgradeable-
            // style signal for a carried item, so there's no reliable max to
            // enforce here. The web UI no longer shows this control for gear
            // items, but block it server-side too in case of a stale/cached
            // tab still POSTing here (same belt-and-suspenders pattern as the
            // basic-module rarity block in HandleSetRarity/
            // HandleInventorySetRarity). Consumables (empty m_TemplateGuid)
            // are unaffected.
            string templateGuid = GetInstanceMemberValue(generatedData, "m_TemplateGuid") as string;
            if (!string.IsNullOrEmpty(templateGuid))
            {
                WriteJson(ctx, 400, "{\"error\":\"Level editing isn't available for weapons while they're in inventory - edit this item's blueprint instead.\"}");
                return;
            }

            bool wrote = TrySetInstanceMemberValue(generatedData, "m_Level", level);
            bool wroteGeneratedBack = wrote && TrySetInstanceMemberValue(item, "m_GeneratedData", generatedData);
            bool wroteBack = wroteGeneratedBack && TryWriteInventoryItemBack(index, item);
            Log($"HandleInventorySetLevel: inventory[{index}] m_Level <- {level}, wrote={wrote}, generatedBack={wroteGeneratedBack}, listBack={wroteBack}.");
            if (wroteBack) SaveNow();
            WriteJson(ctx, 200, "{\"ok\":" + (wroteBack ? "true" : "false") + "}");
        }

        private void HandleInventorySetRarity(HttpListenerContext ctx)
        {
            int index = QueryInt(ctx, "index", -1);
            int modIndex = QueryInt(ctx, "moduleIndex", -1);
            string rarityName = QueryString(ctx, "rarity", null);

            var items = GetInventorySnapshot();
            if (index < 0 || index >= items.Count) { WriteJson(ctx, 400, "{\"error\":\"bad index\"}"); return; }
            object item = items[index];
            object generatedData = GetInstanceMemberValue(item, "m_GeneratedData");
            object target = modIndex < 0 ? generatedData : GetModuleAt(generatedData, modIndex);
            if (target == null) { WriteJson(ctx, 400, "{\"error\":\"bad target\"}"); return; }

            if (modIndex >= 0)
            {
                string targetGuid = GetInstanceMemberValue(target, "m_ModuleGuid") as string;
                var targetCandidate = FindCandidateByGuid(targetGuid);
                if (targetCandidate != null && targetCandidate.IsBasicModule)
                {
                    WriteJson(ctx, 400, "{\"error\":\"Upgradeable Features rarity always matches the item's own rarity - change the item rarity instead, it'll cascade automatically.\"}");
                    return;
                }

                // Per Cameron: limit rarity changes to the module's own
                // valid range (m_MinRarity-m_MaxRarity, same "range: X-Y"
                // tag already shown in the GUI) - the web UI's dropdown no
                // longer offers anything outside it, but block it
                // server-side too in case of a stale/cached tab still
                // POSTing an out-of-range value here.
                if (!_cheatModeEnabled && targetCandidate != null && rarityName != null && !IsRarityWithinRange(targetCandidate.Scriptable, rarityName))
                {
                    WriteJson(ctx, 400, "{\"error\":\"'" + rarityName + "' is outside this module's valid rarity range (" + GetRarityRangeString(targetCandidate.Scriptable) + ") - the game would likely revert it anyway. Enable Cheat Mode to override this.\"}");
                    return;
                }
            }

            if (_itemRarityType == null) _itemRarityType = FindType("Il2CppKeepsake.GeneratedItems.ItemRarity");
            if (_itemRarityType == null || rarityName == null) { WriteJson(ctx, 400, "{\"error\":\"rarity type or value missing\"}"); return; }

            object nextValue;
            try { nextValue = Enum.Parse(_itemRarityType, rarityName, true); }
            catch { WriteJson(ctx, 400, "{\"error\":\"bad rarity name\"}"); return; }

            bool wrote = TrySetInstanceMemberValue(target, "m_Rarity", nextValue);
            if (wrote)
            {
                object after = GetInstanceMemberValue(target, "m_Rarity");
                wrote = after != null && string.Equals(after.ToString(), rarityName, StringComparison.OrdinalIgnoreCase);
            }
            Log($"HandleInventorySetRarity: inventory[{index}] modIndex={modIndex} m_Rarity <- {rarityName}, wrote={wrote} (immediate readback on the SAME object).");
            if (!wrote) { WriteJson(ctx, 200, "{\"ok\":false}"); return; }

            if (modIndex < 0)
            {
                ResizeModulesForRarity(generatedData, rarityName, nextValue);
            }
            else
            {
                TryWriteModuleBack(generatedData, modIndex, target);
            }
            bool wroteGeneratedBack = TrySetInstanceMemberValue(item, "m_GeneratedData", generatedData);
            bool wroteBack = wroteGeneratedBack && TryWriteInventoryItemBack(index, item);
            Log($"HandleInventorySetRarity write-back: generatedBack={wroteGeneratedBack}, listBack={wroteBack}.");
            if (wroteBack) SaveNow();
            WriteJson(ctx, 200, "{\"ok\":" + (wroteBack ? "true" : "false") + "}");
        }

        private void HandleInventorySwapModule(HttpListenerContext ctx)
        {
            int index = QueryInt(ctx, "index", -1);
            int modIndex = QueryInt(ctx, "moduleIndex", -1);
            string guid = QueryString(ctx, "moduleGuid", null);
            if (guid == null) { WriteJson(ctx, 400, "{\"error\":\"missing moduleGuid\"}"); return; }
            if (_moduleCandidates.Count == 0) RefreshModuleCandidates(false);

            ModuleCandidate candidate = null;
            foreach (var c in _moduleCandidates) { if (c.Guid == guid) { candidate = c; break; } }
            if (candidate == null) { WriteJson(ctx, 400, "{\"error\":\"unknown moduleGuid\"}"); return; }

            var items = GetInventorySnapshot();
            if (index < 0 || index >= items.Count) { WriteJson(ctx, 400, "{\"error\":\"bad index\"}"); return; }
            object item = items[index];
            object generatedData = GetInstanceMemberValue(item, "m_GeneratedData");
            object module = GetModuleAt(generatedData, modIndex);
            if (module == null) { WriteJson(ctx, 400, "{\"error\":\"bad moduleIndex\"}"); return; }

            bool wroteGuid = TrySetInstanceMemberValue(module, "m_ModuleGuid", candidate.Guid);
            if (wroteGuid)
            {
                object check = GetInstanceMemberValue(module, "m_ModuleGuid");
                wroteGuid = (check as string) == candidate.Guid;
            }
            Log($"HandleInventorySwapModule: inventory[{index}] module[{modIndex}] wroteGuid={wroteGuid} (immediate readback on the SAME object).");
            if (!wroteGuid) { WriteJson(ctx, 500, "{\"error\":\"could not write m_ModuleGuid (read-only or interop write didn't stick)\"}"); return; }

            try
            {
                object rarityObj = GetInstanceMemberValue(module, "m_Rarity");
                var getTweakables = candidate.Scriptable.GetType().GetMethod("GetTweakableValuesForRarity", BindingFlags.Public | BindingFlags.Instance);
                int rollCount = 1;
                if (getTweakables != null && rarityObj != null)
                {
                    object list = getTweakables.Invoke(candidate.Scriptable, new object[] { rarityObj });
                    var countProp = list == null ? null : list.GetType().GetProperty("Count", BindingFlags.Public | BindingFlags.Instance);
                    if (countProp != null) rollCount = Math.Max(1, (int)countProp.GetValue(list));
                }
                var rollsProp = module.GetType().GetProperty("m_BaseValueRolls", BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Instance);
                if (rollsProp != null)
                {
                    var arrayType = rollsProp.PropertyType;
                    object newArray = Activator.CreateInstance(arrayType, new object[] { rollCount });
                    var itemProp = arrayType.GetProperty("Item", BindingFlags.Public | BindingFlags.Instance);
                    if (itemProp != null)
                        for (int i = 0; i < rollCount; i++) itemProp.SetValue(newArray, 0.5f, new object[] { i });
                    rollsProp.SetValue(module, newArray);
                }
            }
            catch (Exception ex) { Log("HandleInventorySwapModule: m_BaseValueRolls rebuild threw: " + ex.Message); }

            bool wroteModuleBack = TryWriteModuleBack(generatedData, modIndex, module);
            bool wroteGeneratedBack = TrySetInstanceMemberValue(item, "m_GeneratedData", generatedData);
            bool wroteBack = wroteGeneratedBack && TryWriteInventoryItemBack(index, item);
            Log($"HandleInventorySwapModule write-back: moduleBack={wroteModuleBack}, generatedBack={wroteGeneratedBack}, listBack={wroteBack}.");

            if (wroteBack) SaveNow();
            WriteJson(ctx, 200, "{\"ok\":" + (wroteBack ? "true" : "false") + ",\"name\":" + JsonStr(candidate.DisplayName) + "}");
        }

        private void HandleInventoryRerollModule(HttpListenerContext ctx)
        {
            int index = QueryInt(ctx, "index", -1);
            int modIndex = QueryInt(ctx, "moduleIndex", -1);

            var items = GetInventorySnapshot();
            if (index < 0 || index >= items.Count) { WriteJson(ctx, 400, "{\"error\":\"bad index\"}"); return; }
            object item = items[index];
            object generatedData = GetInstanceMemberValue(item, "m_GeneratedData");
            object existingModule = GetModuleAt(generatedData, modIndex);
            if (existingModule == null) { WriteJson(ctx, 400, "{\"error\":\"bad moduleIndex\"}"); return; }
            Type moduleType = existingModule.GetType();

            if (_itemRarityType == null) _itemRarityType = FindType("Il2CppKeepsake.GeneratedItems.ItemRarity");
            object itemRarity = GetInstanceMemberValue(generatedData, "m_Rarity");
            string templateGuid = GetInstanceMemberValue(generatedData, "m_TemplateGuid") as string;
            if (_moduleCandidates.Count == 0) RefreshModuleCandidates(false);

            string existingGuid = GetInstanceMemberValue(existingModule, "m_ModuleGuid") as string;
            var existingCandidate = FindCandidateByGuid(existingGuid);
            bool wantBasic = existingCandidate?.IsBasicModule ?? true;

            object rolledRarity = wantBasic ? itemRarity : RollModuleRarity(itemRarity, _rerollRng);
            string rolledRarityName = rolledRarity?.ToString();

            var byRarity = new List<ModuleCandidate>();
            foreach (var c in _moduleCandidates)
                if (IsRarityWithinRange(c.Scriptable, rolledRarityName)) byRarity.Add(c);
            if (byRarity.Count == 0) byRarity.AddRange(_moduleCandidates);

            var byTemplate = new List<ModuleCandidate>();
            foreach (var c in byRarity)
                if (IsTemplateCompatible(c, templateGuid)) byTemplate.Add(c);
            if (byTemplate.Count == 0) byTemplate.AddRange(byRarity);

            var compatible = new List<ModuleCandidate>();
            foreach (var c in byTemplate)
                if (c.IsBasicModule == wantBasic) compatible.Add(c);
            if (compatible.Count == 0) compatible.AddRange(byTemplate);
            if (compatible.Count == 0) { WriteJson(ctx, 500, "{\"error\":\"no module candidates loaded - try Search Module DB first\"}"); return; }

            var picked = PickWeightedRandomCandidate(compatible, _rerollRng);
            if (picked == null) { WriteJson(ctx, 500, "{\"error\":\"weighted pick failed\"}"); return; }

            object newModule = BuildRerolledModule(moduleType, picked, rolledRarity, _rerollRng);
            if (newModule == null) { WriteJson(ctx, 500, "{\"error\":\"could not construct rerolled module\"}"); return; }

            bool wroteModuleBack = TryWriteModuleBack(generatedData, modIndex, newModule);
            bool wroteGeneratedBack = TrySetInstanceMemberValue(item, "m_GeneratedData", generatedData);
            bool wroteBack = wroteGeneratedBack && TryWriteInventoryItemBack(index, item);
            Log($"HandleInventoryRerollModule: inventory[{index}] module[{modIndex}] rerolled to '{picked.DisplayName}' @ {rolledRarityName} (from {compatible.Count} compatible candidate(s)), listBack={wroteBack}.");

            if (wroteBack) SaveNow();
            WriteJson(ctx, 200, "{\"ok\":" + (wroteBack ? "true" : "false") + ",\"name\":" + JsonStr(picked.DisplayName) + ",\"rarity\":" + JsonStr(rolledRarityName) + "}");
        }

        // Direct roll write for one tweakable stat on an inventory item's
        // module - the slider version of Reroll: instead of picking a whole
        // new random module, just moves this one stat's roll (0-1) to
        // wherever the slider was left, then reports back the true
        // recomputed value (via CalculateRolledValue) so the GUI shows the
        // authoritative number rather than a client-side guess.
        private void HandleSetInventoryModuleRoll(HttpListenerContext ctx)
        {
            int index = QueryInt(ctx, "index", -1);
            int modIndex = QueryInt(ctx, "moduleIndex", -1);
            int tweakableIndex = QueryInt(ctx, "tweakableIndex", -1);
            float roll = QueryFloat(ctx, "roll", -1f);
            if (tweakableIndex < 0 || roll < 0f) { WriteJson(ctx, 400, "{\"error\":\"missing or bad tweakableIndex/roll\"}"); return; }

            var items = GetInventorySnapshot();
            if (index < 0 || index >= items.Count) { WriteJson(ctx, 400, "{\"error\":\"bad index\"}"); return; }
            object item = items[index];
            object generatedData = GetInstanceMemberValue(item, "m_GeneratedData");
            object module = GetModuleAt(generatedData, modIndex);
            if (module == null) { WriteJson(ctx, 400, "{\"error\":\"bad moduleIndex\"}"); return; }

            bool setOk = SetModuleRollValue(module, tweakableIndex, roll);
            bool wroteModuleBack = setOk && TryWriteModuleBack(generatedData, modIndex, module);
            bool wroteGeneratedBack = wroteModuleBack && TrySetInstanceMemberValue(item, "m_GeneratedData", generatedData);
            bool wroteBack = wroteGeneratedBack && TryWriteInventoryItemBack(index, item);
            Log($"HandleSetInventoryModuleRoll: inventory[{index}] module[{modIndex}] tweakable[{tweakableIndex}] roll <- {roll}, wroteBack={wroteBack}.");

            float currentValue = 0f;
            if (wroteBack)
            {
                SaveNow();
                string mGuid = GetInstanceMemberValue(module, "m_ModuleGuid") as string;
                var candidate = FindCandidateByGuid(mGuid);
                if (candidate != null)
                {
                    object mRarity = GetInstanceMemberValue(module, "m_Rarity");
                    object mLevel = GetInstanceMemberValue(module, "m_UpgradeLevel");
                    currentValue = GetSingleTweakableCurrentValue(candidate.Scriptable, mRarity, mLevel, module, tweakableIndex);
                }
            }
            WriteJson(ctx, 200, "{\"ok\":" + (wroteBack ? "true" : "false") + ",\"current\":" + currentValue.ToString(System.Globalization.CultureInfo.InvariantCulture) + "}");
        }

        private void HandleInventoryResetModule(HttpListenerContext ctx)
        {
            int index = QueryInt(ctx, "index", -1);
            int modIndex = QueryInt(ctx, "moduleIndex", -1);

            var items = GetInventorySnapshot();
            if (index < 0 || index >= items.Count) { WriteJson(ctx, 400, "{\"error\":\"bad index\"}"); return; }
            object item = items[index];
            object generatedData = GetInstanceMemberValue(item, "m_GeneratedData");

            string key = ModuleSnapshotKey(InvSnapshotKey(index), modIndex);
            if (!_originalModuleSnapshots.TryGetValue(key, out var snap))
            {
                WriteJson(ctx, 400, "{\"error\":\"no original value captured for this module yet - open/refresh the inventory list once before editing it\"}");
                return;
            }

            bool ok = ApplyModuleSnapshot(generatedData, modIndex, snap);
            bool wroteGeneratedBack = TrySetInstanceMemberValue(item, "m_GeneratedData", generatedData);
            bool wroteBack = wroteGeneratedBack && TryWriteInventoryItemBack(index, item);
            Log($"HandleInventoryResetModule: inventory[{index}] module[{modIndex}] reset to original, applySnapshot={ok}, listBack={wroteBack}.");
            if (wroteBack) SaveNow();
            WriteJson(ctx, 200, "{\"ok\":" + (wroteBack ? "true" : "false") + "}");
        }

        private void HandleInventoryResetAllModules(HttpListenerContext ctx)
        {
            int index = QueryInt(ctx, "index", -1);

            var items = GetInventorySnapshot();
            if (index < 0 || index >= items.Count) { WriteJson(ctx, 400, "{\"error\":\"bad index\"}"); return; }
            object item = items[index];
            object generatedData = GetInstanceMemberValue(item, "m_GeneratedData");

            int moduleCount = GetModuleCount(generatedData);
            int resetCount = 0;
            for (int m = 0; m < moduleCount; m++)
            {
                string key = ModuleSnapshotKey(InvSnapshotKey(index), m);
                if (_originalModuleSnapshots.TryGetValue(key, out var snap))
                {
                    if (ApplyModuleSnapshot(generatedData, m, snap)) resetCount++;
                }
            }
            bool wroteGeneratedBack = TrySetInstanceMemberValue(item, "m_GeneratedData", generatedData);
            bool wroteBack = wroteGeneratedBack && TryWriteInventoryItemBack(index, item);
            Log($"HandleInventoryResetAllModules: inventory[{index}] reset {resetCount}/{moduleCount} module(s) to original, listBack={wroteBack}.");
            if (resetCount > 0 && wroteBack) SaveNow();
            WriteJson(ctx, 200, "{\"ok\":true,\"resetCount\":" + resetCount + ",\"moduleCount\":" + moduleCount + "}");
        }

        private void HandleInventorySwapCosmetic(HttpListenerContext ctx)
        {
            int index = QueryInt(ctx, "index", -1);
            int cosmeticIndex = QueryInt(ctx, "cosmeticIndex", -1);
            string cosmeticGuid = QueryString(ctx, "cosmeticGuid", null);
            if (cosmeticGuid == null) { WriteJson(ctx, 400, "{\"error\":\"missing cosmeticGuid\"}"); return; }
            if (_cosmeticCandidates.Count == 0) RefreshCosmeticCandidates();

            CosmeticCandidate candidate = null;
            foreach (var c in _cosmeticCandidates) { if (c.Guid == cosmeticGuid) { candidate = c; break; } }
            if (candidate == null) { WriteJson(ctx, 400, "{\"error\":\"unknown cosmeticGuid\"}"); return; }

            var items = GetInventorySnapshot();
            if (index < 0 || index >= items.Count) { WriteJson(ctx, 400, "{\"error\":\"bad index\"}"); return; }
            object item = items[index];
            object generatedData = GetInstanceMemberValue(item, "m_GeneratedData");
            object cosmetic = GetCosmeticAt(generatedData, cosmeticIndex);
            if (cosmetic == null) { WriteJson(ctx, 400, "{\"error\":\"bad cosmeticIndex\"}"); return; }

            object existingSlotType = GetInstanceMemberValue(cosmetic, "m_SlotType");
            string existingSlotTypeName = existingSlotType?.ToString();
            if (!string.IsNullOrEmpty(existingSlotTypeName) && !string.IsNullOrEmpty(candidate.SlotType)
                && !string.Equals(existingSlotTypeName, candidate.SlotType, StringComparison.OrdinalIgnoreCase))
            {
                WriteJson(ctx, 400, "{\"error\":\"slot type mismatch: this slot is '" + existingSlotTypeName + "', that cosmetic is '" + candidate.SlotType + "'\"}");
                return;
            }

            bool wroteGuid = TrySetInstanceMemberValue(cosmetic, "m_CosmeticGuid", candidate.Guid);
            if (wroteGuid)
            {
                object check = GetInstanceMemberValue(cosmetic, "m_CosmeticGuid");
                wroteGuid = (check as string) == candidate.Guid;
            }
            Log($"HandleInventorySwapCosmetic: inventory[{index}] cosmetic[{cosmeticIndex}] wroteGuid={wroteGuid} (immediate readback on the SAME object).");
            if (!wroteGuid) { WriteJson(ctx, 500, "{\"error\":\"could not write m_CosmeticGuid (read-only or interop write didn't stick)\"}"); return; }

            bool wroteCosmeticBack = TryWriteCosmeticBack(generatedData, cosmeticIndex, cosmetic);
            bool wroteGeneratedBack = TrySetInstanceMemberValue(item, "m_GeneratedData", generatedData);
            bool wroteBack = wroteGeneratedBack && TryWriteInventoryItemBack(index, item);
            Log($"HandleInventorySwapCosmetic write-back: cosmeticBack={wroteCosmeticBack}, generatedBack={wroteGeneratedBack}, listBack={wroteBack}.");

            if (wroteBack) SaveNow();
            WriteJson(ctx, 200, "{\"ok\":" + (wroteBack ? "true" : "false") + ",\"name\":" + JsonStr(candidate.DisplayName) + "}");
        }

        private void HandleInventoryResetCosmetic(HttpListenerContext ctx)
        {
            int index = QueryInt(ctx, "index", -1);
            int cosmeticIndex = QueryInt(ctx, "cosmeticIndex", -1);

            var items = GetInventorySnapshot();
            if (index < 0 || index >= items.Count) { WriteJson(ctx, 400, "{\"error\":\"bad index\"}"); return; }
            object item = items[index];
            object generatedData = GetInstanceMemberValue(item, "m_GeneratedData");

            string key = CosmeticSnapshotKey(InvSnapshotKey(index), cosmeticIndex);
            if (!_originalCosmeticSnapshots.TryGetValue(key, out var snap))
            {
                WriteJson(ctx, 400, "{\"error\":\"no original value captured for this cosmetic slot yet - open/refresh the inventory list once before editing it\"}");
                return;
            }

            bool ok = ApplyCosmeticSnapshot(generatedData, cosmeticIndex, snap);
            bool wroteGeneratedBack = TrySetInstanceMemberValue(item, "m_GeneratedData", generatedData);
            bool wroteBack = wroteGeneratedBack && TryWriteInventoryItemBack(index, item);
            Log($"HandleInventoryResetCosmetic: inventory[{index}] cosmetic[{cosmeticIndex}] reset to original, applySnapshot={ok}, listBack={wroteBack}.");
            if (wroteBack) SaveNow();
            WriteJson(ctx, 200, "{\"ok\":" + (wroteBack ? "true" : "false") + "}");
        }

        // Whole-item undo for one inventory slot - restores templateGuid/
        // consumable guid, rarity, level, every module, and every cosmetic
        // back to their session-start snapshot. Adapted from the inventory
        // loop inside HandleResetEverything, just scoped to a single index
        // instead of looping over the whole list. Deliberately NOT resetting
        // m_ResourceAmount/m_AmmoInMag, matching HandleResetEverything's own
        // behavior (currencies/ammo are treated as a separate concern).
        private void HandleInventoryResetItem(HttpListenerContext ctx)
        {
            int index = QueryInt(ctx, "index", -1);
            if (_itemRarityType == null) _itemRarityType = FindType("Il2CppKeepsake.GeneratedItems.ItemRarity");

            var items = GetInventorySnapshot();
            if (index < 0 || index >= items.Count) { WriteJson(ctx, 400, "{\"error\":\"bad index\"}"); return; }
            object item = items[index];
            object generatedData = GetInstanceMemberValue(item, "m_GeneratedData");
            string invKey = InvSnapshotKey(index);
            bool touched = false;

            if (_originalItemSnapshots.TryGetValue(invKey, out var itemSnap))
            {
                if (!string.IsNullOrEmpty(itemSnap.TemplateGuid))
                {
                    string currentTemplateGuid = GetInstanceMemberValue(generatedData, "m_TemplateGuid") as string;
                    if (currentTemplateGuid != itemSnap.TemplateGuid)
                    {
                        if (TrySetInstanceMemberValue(generatedData, "m_TemplateGuid", itemSnap.TemplateGuid)) touched = true;
                    }
                }
                if (!string.IsNullOrEmpty(itemSnap.ConsumableGuid))
                {
                    string currentConsumableGuid = GetInstanceMemberValue(item, "m_GUID") as string;
                    if (currentConsumableGuid != itemSnap.ConsumableGuid)
                    {
                        if (TrySetInstanceMemberValue(item, "m_GUID", itemSnap.ConsumableGuid)) touched = true;
                    }
                }
                if (itemSnap.Rarity != null && _itemRarityType != null)
                {
                    object rarityValue = null;
                    try { rarityValue = Enum.Parse(_itemRarityType, itemSnap.Rarity, true); }
                    catch (Exception ex) { Log($"HandleInventoryResetItem: Enum.Parse rarity '{itemSnap.Rarity}' threw: {ex.Message}"); }
                    if (rarityValue != null)
                    {
                        if (TrySetInstanceMemberValue(generatedData, "m_Rarity", rarityValue)) touched = true;
                        ResizeModulesForRarity(generatedData, itemSnap.Rarity, rarityValue);
                    }
                }
                if (TrySetInstanceMemberValue(generatedData, "m_Level", itemSnap.Level)) touched = true;
            }

            int moduleCount = GetModuleCount(generatedData);
            int modulesReset = 0;
            for (int m = 0; m < moduleCount; m++)
            {
                string key = ModuleSnapshotKey(invKey, m);
                if (_originalModuleSnapshots.TryGetValue(key, out var modSnap))
                {
                    if (ApplyModuleSnapshot(generatedData, m, modSnap)) { modulesReset++; touched = true; }
                }
            }

            int cosmeticCount = GetCosmeticCount(generatedData);
            int cosmeticsReset = 0;
            for (int c = 0; c < cosmeticCount; c++)
            {
                string key = CosmeticSnapshotKey(invKey, c);
                if (_originalCosmeticSnapshots.TryGetValue(key, out var cosSnap))
                {
                    if (ApplyCosmeticSnapshot(generatedData, c, cosSnap)) { cosmeticsReset++; touched = true; }
                }
            }

            bool wroteGeneratedBack = TrySetInstanceMemberValue(item, "m_GeneratedData", generatedData);
            bool wroteBack = wroteGeneratedBack && TryWriteInventoryItemBack(index, item);
            Log($"HandleInventoryResetItem: inventory[{index}] reset to original - touched={touched}, modulesReset={modulesReset}, cosmeticsReset={cosmeticsReset}, listBack={wroteBack}.");
            if (wroteBack) SaveNow();
            WriteJson(ctx, 200, "{\"ok\":" + (wroteBack ? "true" : "false") + ",\"modulesReset\":" + modulesReset + ",\"cosmeticsReset\":" + cosmeticsReset + "}");
        }

        // ---------- HTTP plumbing helpers ----------

        private static int QueryInt(HttpListenerContext ctx, string key, int fallback)
        {
            string s = ctx.Request.QueryString[key];
            int v;
            return (s != null && int.TryParse(s, out v)) ? v : fallback;
        }

        private static string QueryString(HttpListenerContext ctx, string key, string fallback)
        {
            string s = ctx.Request.QueryString[key];
            return s ?? fallback;
        }

        private static float QueryFloat(HttpListenerContext ctx, string key, float fallback)
        {
            string s = ctx.Request.QueryString[key];
            float v;
            return (s != null && float.TryParse(s, System.Globalization.NumberStyles.Float, System.Globalization.CultureInfo.InvariantCulture, out v)) ? v : fallback;
        }

        private static void WriteJson(HttpListenerContext ctx, int statusCode, string json)
        {
            ctx.Response.StatusCode = statusCode;
            ctx.Response.ContentType = "application/json";
            var bytes = Encoding.UTF8.GetBytes(json);
            ctx.Response.ContentLength64 = bytes.Length;
            ctx.Response.OutputStream.Write(bytes, 0, bytes.Length);
            ctx.Response.OutputStream.Close();
        }

        private void ServeStaticFile(HttpListenerContext ctx, string fileName, string contentType)
        {
            try
            {
                var dir = Path.GetDirectoryName(Assembly.GetExecutingAssembly().Location);
                var path = Path.Combine(dir ?? ".", fileName);
                var bytes = File.ReadAllBytes(path);
                ctx.Response.StatusCode = 200;
                ctx.Response.ContentType = contentType;
                ctx.Response.ContentLength64 = bytes.Length;
                ctx.Response.OutputStream.Write(bytes, 0, bytes.Length);
                ctx.Response.OutputStream.Close();
            }
            catch (Exception ex)
            {
                WriteJson(ctx, 500, "{\"error\":" + JsonStr("Could not serve " + fileName + ": " + ex.Message) + "}");
            }
        }

        private static string JsonEscape(string s)
        {
            if (s == null) return "";
            var sb = new StringBuilder();
            foreach (char c in s)
            {
                switch (c)
                {
                    case '"': sb.Append("\\\""); break;
                    case '\\': sb.Append("\\\\"); break;
                    case '\n': sb.Append("\\n"); break;
                    case '\r': sb.Append("\\r"); break;
                    case '\t': sb.Append("\\t"); break;
                    default:
                        if (c < 0x20) sb.Append("\\u").Append(((int)c).ToString("x4"));
                        else sb.Append(c);
                        break;
                }
            }
            return sb.ToString();
        }

        private static string JsonStr(string s)
        {
            return s == null ? "null" : "\"" + JsonEscape(s) + "\"";
        }

        private static string JsonStrArray(List<string> values)
        {
            if (values == null || values.Count == 0) return "[]";
            var sb = new StringBuilder("[");
            for (int i = 0; i < values.Count; i++)
            {
                if (i > 0) sb.Append(",");
                sb.Append(JsonStr(values[i]));
            }
            sb.Append("]");
            return sb.ToString();
        }

        private static int SafeInt(object o)
        {
            try { return Convert.ToInt32(o); } catch { return 0; }
        }

        public override void OnUpdate()
        {
            if (_mgrType == null) return;
            var kb = Keyboard.current;
            if (kb == null) return;

            try
            {
                // Only 4 keybinds total, on purpose, F5-F8 as one contiguous
                // block: F5 = Refresh lives in the browser tab (see
                // EditorUI.html - not a Unity/game key at all), F6-F8 are
                // these 3 in-game ones. Everything else (selection cursors,
                // per-item edits, module browsing/swap, debug dumps) now
                // goes through the web UI only.
                if (kb.f6Key.wasPressedThisFrame) SaveNow();
                if (kb.f7Key.wasPressedThisFrame) AddCredits();
                if (kb.f8Key.wasPressedThisFrame) AddAllIngots();
            }
            catch (Exception ex)
            {
                MelonLogger.Error("Editor action failed: " + ex);
            }

            ProcessPendingHttpRequests();
        }

        // ---------- selection ----------

        private void MoveBlueprintSelection(int delta)
        {
            var blueprints = GetBlueprintsSnapshot();
            if (blueprints.Count == 0) { Log("No blueprints found (are you in a save?)."); return; }
            _selectedBlueprintIndex = Wrap(_selectedBlueprintIndex + delta, blueprints.Count);
            _selectedModuleIndex = -1;
            PrintSelection(blueprints);
        }

        private void MoveModuleSelection(int delta)
        {
            var blueprints = GetBlueprintsSnapshot();
            if (_selectedBlueprintIndex >= blueprints.Count) { Log("Selection out of range, press F7 to refresh."); return; }
            object bp = blueprints[_selectedBlueprintIndex];
            object generatedData = GetInstanceMemberValue(bp, "m_GeneratedData");
            int moduleCount = GetModuleCount(generatedData);
            // range is -1 (whole item) .. moduleCount-1
            _selectedModuleIndex = Wrap(_selectedModuleIndex + 1 + delta, moduleCount + 1) - 1;
            PrintSelection(blueprints);
        }

        private static int Wrap(int value, int count)
        {
            if (count <= 0) return 0;
            int m = value % count;
            if (m < 0) m += count;
            return m;
        }

        private void PrintSelection(List<object> blueprints)
        {
            if (_selectedBlueprintIndex >= blueprints.Count) return;
            object bp = blueprints[_selectedBlueprintIndex];
            object generatedData = GetInstanceMemberValue(bp, "m_GeneratedData");
            string name = AsString(GetInstanceMemberValue(generatedData, "ResolvedName"));

            if (_selectedModuleIndex < 0)
            {
                object rarity = GetInstanceMemberValue(generatedData, "m_Rarity");
                object level = GetInstanceMemberValue(generatedData, "m_Level");
                Log($"Selected [{_selectedBlueprintIndex}] {name}  (whole item)  Rarity={rarity} Level={level}");
            }
            else
            {
                object module = GetModuleAt(generatedData, _selectedModuleIndex);
                if (module == null) { Log("Module index out of range."); return; }
                object rarity = GetInstanceMemberValue(module, "m_Rarity");
                object level = GetInstanceMemberValue(module, "m_UpgradeLevel");
                Log($"Selected [{_selectedBlueprintIndex}] {name}  module[{_selectedModuleIndex}]  Rarity={rarity} Level={level}");
            }
        }

        // ---------- actions ----------

        private void UpgradeSelectedTargetLevel()
        {
            var blueprints = GetBlueprintsSnapshot();
            if (_selectedBlueprintIndex >= blueprints.Count) { Log("No blueprint selected. Press F7 then PageUp/PageDown."); return; }
            object bp = blueprints[_selectedBlueprintIndex];

            if (_selectedModuleIndex < 0)
            {
                var m = _mgrType.GetMethod("TryUpgradeBlueprint", BindingFlags.Public | BindingFlags.Static);
                if (m == null) { Log("TryUpgradeBlueprint method not found."); return; }
                object result = m.Invoke(null, new object[] { bp });
                Log("TryUpgradeBlueprint -> " + result);
            }
            else
            {
                var m = _mgrType.GetMethod("TryModifyBlueprintModuleLevel", BindingFlags.Public | BindingFlags.Static);
                if (m == null) { Log("TryModifyBlueprintModuleLevel method not found."); return; }
                object result = m.Invoke(null, new object[] { bp, _selectedModuleIndex, 1 });
                Log("TryModifyBlueprintModuleLevel -> " + result);
            }

            SaveNow();
            PrintSelection(blueprints);
        }

        private void CycleSelectedTargetRarity()
        {
            var blueprints = GetBlueprintsSnapshot();
            if (_selectedBlueprintIndex >= blueprints.Count) { Log("No blueprint selected. Press F7 then PageUp/PageDown."); return; }
            object bp = blueprints[_selectedBlueprintIndex];
            object generatedData = GetInstanceMemberValue(bp, "m_GeneratedData");

            object target = _selectedModuleIndex < 0 ? generatedData : GetModuleAt(generatedData, _selectedModuleIndex);
            if (target == null) { Log("Nothing to modify at current selection."); return; }

            if (_itemRarityType == null)
                _itemRarityType = FindType("Il2CppKeepsake.GeneratedItems.ItemRarity");
            if (_itemRarityType == null) { Log("ItemRarity type not found."); return; }

            var prop = target.GetType().GetProperty("m_Rarity", BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Instance);
            if (prop == null) { Log("m_Rarity property not found on " + target.GetType().FullName); return; }

            object before = prop.GetValue(target);
            int currentInt = Convert.ToInt32(before);
            int nextInt = (currentInt + 1) % 4; // Common=0 Rare=1 Epic=2 Legendary=3 (Count=4 skipped)
            object nextValue = Enum.ToObject(_itemRarityType, nextInt);

            bool wrote = false;
            Log($"m_Rarity: CanRead={prop.CanRead} CanWrite={prop.CanWrite}");
            if (prop.CanWrite)
            {
                try { prop.SetValue(target, nextValue); wrote = true; }
                catch (Exception ex) { Log("Property SetValue threw: " + ex.Message); }
            }

            if (!wrote)
            {
                // Some IL2CPP interop wrappers only surface a getter on the PropertyInfo
                // even when a real setter method exists underneath - try invoking it
                // directly as a fallback before giving up.
                var setter = target.GetType().GetMethod("set_m_Rarity", BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Instance);
                if (setter != null)
                {
                    try { setter.Invoke(target, new object[] { nextValue }); wrote = true; }
                    catch (Exception ex) { Log("set_m_Rarity invoke threw: " + ex.Message); }
                }
                else
                {
                    Log("No set_m_Rarity method found either.");
                }
            }

            object after = prop.GetValue(target);
            bool confirmed = Convert.ToInt32(after) == nextInt;
            Log($"[UNOFFICIAL] Rarity: before={before} attempted={nextValue} after-read-back={after}. {(confirmed ? "Write confirmed." : "WRITE DID NOT STICK - tell me this exact log line and I'll dig into why.")}");

            if (confirmed) SaveNow();
            PrintSelection(blueprints);
        }

        private void AddCredits()
        {
            var creditsCurrencyProp = _mgrType.GetProperty("CreditsCurrency", BindingFlags.Public | BindingFlags.Static);
            var modifyMethod = _mgrType.GetMethod("ModifyCurrency", BindingFlags.Public | BindingFlags.Static);
            var getMethod = _mgrType.GetMethod("GetCurrency", BindingFlags.Public | BindingFlags.Static);
            if (creditsCurrencyProp == null || modifyMethod == null) { Log("CreditsCurrency/ModifyCurrency not found."); return; }

            object currency = creditsCurrencyProp.GetValue(null);
            try
            {
                modifyMethod.Invoke(null, new object[] { currency, 25000 });
                int newAmount = getMethod != null ? (int)getMethod.Invoke(null, new object[] { currency }) : -1;
                Log($"Credits += 25,000 -> now {newAmount}");
            }
            catch (Exception ex)
            {
                Log("ModifyCurrency (credits) failed: " + ex.Message);
            }
        }

        // One keypress bumps every ingot tier at once, biggest amount on the
        // most common tier down to the smallest amount on the rarest -
        // Crude (index 0, least rare) +20, Flawed +15, Pure +10, Flawless
        // +5, Pristine (index 4, most rare) +1. Reuses AddToIngot's own
        // ModifyCurrency call per tier rather than duplicating it.
        private static readonly int[] IngotAddAmounts = { 20, 15, 10, 5, 1 };

        private void AddAllIngots()
        {
            var ingots = GetIngotCurrencies();
            for (int i = 0; i < ingots.Count && i < IngotAddAmounts.Length; i++)
                AddToIngot(i, IngotAddAmounts[i]);
        }

        private List<object> GetIngotCurrencies()
        {
            var ingotsProp = _mgrType.GetProperty("IngotCurrencies", BindingFlags.Public | BindingFlags.Static);
            if (ingotsProp == null) { Log("IngotCurrencies property not found on MetaProgressionManager."); return new List<object>(); }

            object ingots;
            try { ingots = ingotsProp.GetValue(null); }
            catch (Exception ex) { Log("IngotCurrencies getter threw: " + ex.Message); return new List<object>(); }
            if (ingots == null) { Log("IngotCurrencies returned null."); return new List<object>(); }

            return ReadIndexedCollection(ingots);
        }

        private static string CurrencyDisplayName(object currency)
        {
            return GetInstanceMemberValue(currency, "DisplayName") as string
                   ?? GetInstanceMemberValue(currency, "Name") as string
                   ?? currency.ToString();
        }

        // User-confirmed names for the 5 ingot currencies, in the order
        // IngotCurrencies returns them (confirmed by matching the amounts
        // in their save: 255, 157, 107, 82, 1 against this list top-to-bottom).
        // The reflected DisplayName/Name properties above weren't resolving to
        // anything useful, so these are used as the primary source and the
        // reflected name is just a fallback for any ingot beyond index 4.
        private static readonly string[] IngotDisplayNameOverride = {
            "Crude Materia Ingots",
            "Flawed Materia Ingots",
            "Pure Materia Ingots",
            "Flawless Materia Ingots",
            "Pristine Materia Ingot"
        };

        private static string IngotDisplayName(int index, object currency)
        {
            if (index >= 0 && index < IngotDisplayNameOverride.Length) return IngotDisplayNameOverride[index];
            return CurrencyDisplayName(currency);
        }

        private void ListCurrencies()
        {
            var getMethod = _mgrType.GetMethod("GetCurrency", BindingFlags.Public | BindingFlags.Static);
            var creditsCurrencyProp = _mgrType.GetProperty("CreditsCurrency", BindingFlags.Public | BindingFlags.Static);
            if (creditsCurrencyProp != null && getMethod != null)
            {
                object credits = creditsCurrencyProp.GetValue(null);
                try
                {
                    int amt = (int)getMethod.Invoke(null, new object[] { credits });
                    Log($"Credits = {amt}   (set from the web UI's Currencies panel)");
                }
                catch (Exception ex) { Log("Reading credits failed: " + ex.Message); }
            }

            var ingots = GetIngotCurrencies();
            for (int i = 0; i < ingots.Count; i++)
            {
                string name = IngotDisplayName(i, ingots[i]);
                int amt = -1;
                if (getMethod != null)
                {
                    try { amt = (int)getMethod.Invoke(null, new object[] { ingots[i] }); }
                    catch (Exception ex) { Log($"Reading ingot[{i}] failed: " + ex.Message); }
                }
                Log($"Ingot[{i}] '{name}' = {amt}   (Ctrl+{i + 1} adds 10)");
            }
        }

        private void AddToIngot(int index, int amount)
        {
            var ingots = GetIngotCurrencies();
            if (index < 0 || index >= ingots.Count) { Log($"Ingot index {index} out of range (found {ingots.Count} ingot currencies - press Home to list them)."); return; }
            object currency = ingots[index];

            var modifyMethod = _mgrType.GetMethod("ModifyCurrency", BindingFlags.Public | BindingFlags.Static);
            var getMethod = _mgrType.GetMethod("GetCurrency", BindingFlags.Public | BindingFlags.Static);
            if (modifyMethod == null) { Log("ModifyCurrency not found."); return; }

            try
            {
                modifyMethod.Invoke(null, new object[] { currency, amount });
                int newAmount = getMethod != null ? (int)getMethod.Invoke(null, new object[] { currency }) : -1;
                string name = IngotDisplayName(index, currency);
                Log($"Ingot[{index}] '{name}' += {amount} -> now {newAmount}");
            }
            catch (Exception ex)
            {
                Log("ModifyCurrency (ingot) failed: " + ex.Message);
            }
        }

        private void SaveNow()
        {
            // First save of this mod session: snapshot whatever's already on
            // disk BEFORE this edit lands, so there's always a "how it was
            // when I started touching things this session" backup to fall
            // back to, without the user having to remember to do it
            // themselves. See the backup/restore system below.
            if (!_autoBackupDoneThisSession)
            {
                _autoBackupDoneThisSession = true;
                CreateBackup("session-start");
            }

            var m = _mgrType.GetMethod("SaveDataToCloud", BindingFlags.Public | BindingFlags.Static);
            if (m == null) { Log("SaveDataToCloud not found."); return; }
            m.Invoke(null, null);
            Log("SaveDataToCloud() called.");
        }

        // ---------- backup / restore system ----------

        // Inspired by JumpSaves' BackupStore.cs (github.com/gurudennis/
        // JumpSaves, MIT licensed) - a timestamped-folder-per-backup pattern
        // for the same save file this game uses. One real difference from
        // JumpSaves: that tool is an OFFLINE editor (only ever runs while
        // Jump Space is closed) that edits the save file directly, so a
        // restore takes effect immediately. This mod edits a LIVE save while
        // the game is running via reflection and calls the game's own
        // SaveDataToCloud() to persist changes - it never writes
        // persistent_user_data.bin itself. That means restoring a backup
        // here only overwrites the file ON DISK; the currently running game
        // session has its own copy in memory and won't notice until you
        // close and reopen the save (or restart the game). HandleRestoreBackup
        // says as much in its response so the UI can surface it.
        private static string _cachedSaveFilePath = null;
        private bool _autoBackupDoneThisSession = false;
        private const int MaxBackups = 20;

        private static string BackupsDir
        {
            get
            {
                var dir = Path.GetDirectoryName(Assembly.GetExecutingAssembly().Location);
                return Path.Combine(dir ?? ".", "JumpSpaceEditorBackups");
            }
        }

        // Jump Space's actual save file (persistent_user_data.bin) lives in
        // Steam's per-user cloud-sync mirror folder, NOT anywhere under the
        // game's own install directory - confirmed via JumpSaves' SaveDir.cs,
        // which reverse-engineered this path from the game's real Steam
        // Cloud behavior (userdata/{steamid}/1757300/remote/). The Steam
        // CLIENT install location (where "userdata" lives) is independent of
        // whatever drive this game's own library happens to be on, so it
        // can't be derived from this DLL's own folder - it has to be found
        // directly. Checked against a handful of common Steam client install
        // locations rather than reading the Windows registry (like JumpSaves
        // does), to avoid pulling in a Microsoft.Win32.Registry package
        // reference just for this one lookup.
        private string FindSaveFilePath()
        {
            if (_cachedSaveFilePath != null && File.Exists(_cachedSaveFilePath)) return _cachedSaveFilePath;

            var candidateSteamDirs = new List<string>();
            foreach (var drive in new[] { "C", "D", "E", "F", "G", "H" })
            {
                candidateSteamDirs.Add(drive + @":\Program Files (x86)\Steam");
                candidateSteamDirs.Add(drive + @":\Steam");
                candidateSteamDirs.Add(drive + @":\SteamLibrary\Steam");
            }

            foreach (var steamDir in candidateSteamDirs)
            {
                string userDataRoot = Path.Combine(steamDir, "userdata");
                if (!Directory.Exists(userDataRoot)) continue;
                try
                {
                    foreach (var userDir in Directory.GetDirectories(userDataRoot))
                    {
                        string saveFile = Path.Combine(userDir, "1757300", "remote", "persistent_user_data.bin");
                        if (File.Exists(saveFile))
                        {
                            _cachedSaveFilePath = saveFile;
                            return saveFile;
                        }
                    }
                }
                catch (Exception ex) { Log("FindSaveFilePath: scanning " + userDataRoot + " threw: " + ex.Message); }
            }

            return null;
        }

        // Copies the current on-disk save into a new timestamped folder
        // under BackupsDir, alongside a small metadata.json (mirroring
        // JumpSaves' Backup/BackupStore shape, simplified to what this mod
        // actually needs - no rename support). Returns the new folder's name
        // on success, or null if the save file couldn't be found or the copy
        // failed (both logged either way).
        private string CreateBackup(string label)
        {
            string saveFile = FindSaveFilePath();
            if (saveFile == null)
            {
                Log("CreateBackup: could not locate persistent_user_data.bin under any Steam userdata folder.");
                return null;
            }

            try
            {
                Directory.CreateDirectory(BackupsDir);
                string stamp = DateTime.Now.ToString("yyyy-MM-dd_HH-mm-ss");
                string folderName = string.IsNullOrEmpty(label) ? stamp : (stamp + "_" + label);
                string folderPath = Path.Combine(BackupsDir, folderName);
                Directory.CreateDirectory(folderPath);
                string destFile = Path.Combine(folderPath, "persistent_user_data.bin");
                File.Copy(saveFile, destFile, true);

                string metaPath = Path.Combine(folderPath, "metadata.json");
                File.WriteAllText(metaPath,
                    "{\"timestamp\":" + JsonStr(DateTime.Now.ToString("o")) +
                    ",\"originalPath\":" + JsonStr(saveFile) +
                    ",\"label\":" + JsonStr(label) + "}");

                Log($"CreateBackup: backed up '{saveFile}' -> '{destFile}'.");
                PruneBackups();
                return folderName;
            }
            catch (Exception ex)
            {
                Log("CreateBackup failed: " + ex.Message);
                return null;
            }
        }

        // Keeps only the MaxBackups most recent backup folders - same
        // pruning concept as JumpSaves' BackupStore.MaxBackups, just fixed
        // instead of user-configurable, to keep this simple.
        private void PruneBackups()
        {
            try
            {
                if (!Directory.Exists(BackupsDir)) return;
                var dirs = new List<DirectoryInfo>(new DirectoryInfo(BackupsDir).GetDirectories());
                dirs.Sort((a, b) => b.CreationTimeUtc.CompareTo(a.CreationTimeUtc));
                for (int i = MaxBackups; i < dirs.Count; i++)
                {
                    try { dirs[i].Delete(true); Log("PruneBackups: removed old backup " + dirs[i].Name); }
                    catch (Exception ex) { Log("PruneBackups: failed to delete " + dirs[i].Name + ": " + ex.Message); }
                }
            }
            catch (Exception ex) { Log("PruneBackups failed: " + ex.Message); }
        }

        private string BuildBackupsJson()
        {
            var sb = new StringBuilder();
            sb.Append("[");
            try
            {
                if (Directory.Exists(BackupsDir))
                {
                    var dirs = new List<DirectoryInfo>(new DirectoryInfo(BackupsDir).GetDirectories());
                    dirs.Sort((a, b) => b.CreationTimeUtc.CompareTo(a.CreationTimeUtc));
                    for (int i = 0; i < dirs.Count; i++)
                    {
                        if (i > 0) sb.Append(",");
                        var d = dirs[i];
                        string saveFile = Path.Combine(d.FullName, "persistent_user_data.bin");
                        long size = File.Exists(saveFile) ? new FileInfo(saveFile).Length : 0;
                        sb.Append("{\"name\":").Append(JsonStr(d.Name))
                          .Append(",\"createdAt\":").Append(JsonStr(d.CreationTime.ToString("o")))
                          .Append(",\"sizeBytes\":").Append(size)
                          .Append("}");
                    }
                }
            }
            catch (Exception ex) { Log("BuildBackupsJson failed: " + ex.Message); }
            sb.Append("]");
            return sb.ToString();
        }

        private void HandleCreateBackup(HttpListenerContext ctx)
        {
            string label = ctx.Request.QueryString["label"];
            string name = CreateBackup(string.IsNullOrEmpty(label) ? "manual" : label);
            if (name == null)
            {
                WriteJson(ctx, 500, "{\"error\":\"Could not create a backup - persistent_user_data.bin wasn't found under any Steam userdata folder. See Editor_Log.txt for details.\"}");
                return;
            }
            WriteJson(ctx, 200, "{\"ok\":true,\"name\":" + JsonStr(name) + "}");
        }

        private void HandleRestoreBackup(HttpListenerContext ctx)
        {
            string name = ctx.Request.QueryString["name"];
            if (string.IsNullOrEmpty(name)) { WriteJson(ctx, 400, "{\"error\":\"Missing 'name'.\"}"); return; }

            // Guard against path traversal - the folder we open has to be a
            // direct, exact-name child of BackupsDir, nothing else.
            string folderPath = Path.Combine(BackupsDir, name);
            if (!Directory.Exists(folderPath) || Path.GetFileName(folderPath) != name)
            {
                WriteJson(ctx, 404, "{\"error\":\"Backup not found.\"}");
                return;
            }

            string backupFile = Path.Combine(folderPath, "persistent_user_data.bin");
            if (!File.Exists(backupFile)) { WriteJson(ctx, 404, "{\"error\":\"Backup folder is missing its save file.\"}"); return; }

            string saveFile = FindSaveFilePath();
            if (saveFile == null) { WriteJson(ctx, 500, "{\"error\":\"Could not locate the live save file to restore over.\"}"); return; }

            try
            {
                // Safety-net: back up whatever's on disk RIGHT NOW before
                // overwriting it, labeled so it's obviously not a normal
                // backup - undoes a bad restore choice the same way every
                // other Reset button in this mod does.
                CreateBackup("before-restore");
                File.Copy(backupFile, saveFile, true);
                Log($"HandleRestoreBackup: restored '{backupFile}' -> '{saveFile}'.");
                WriteJson(ctx, 200, "{\"ok\":true,\"note\":\"Restored to disk. This only takes effect on your NEXT load - close and reopen the save (or restart the game) to see it. The currently running session is unaffected until then, and will overwrite this restore again the next time anything in the game (or this mod) autosaves.\"}");
            }
            catch (Exception ex)
            {
                Log("HandleRestoreBackup failed: " + ex.Message);
                WriteJson(ctx, 500, "{\"error\":" + JsonStr("Restore failed: " + ex.Message) + "}");
            }
        }

        // ---------- Cheat Mode ----------
        //
        // A single session-scoped switch (resets to off on every mod
        // reload/game restart - deliberately not persisted anywhere, so it's
        // never silently "still on" from a previous session) that relaxes
        // three limits this mod normally enforces:
        //   1. Module roll ceiling: SetModuleRollValue clamps to 0-1
        //      normally (a real roll always is); Cheat Mode raises that to
        //      CheatModeRollCeiling (300%).
        //   2. Rarity range: HandleSetRarity/HandleInventorySetRarity
        //      normally reject a rarity outside the module's own valid
        //      range (m_MinRarity-m_MaxRarity); Cheat Mode skips that check.
        //   3. Module level: previously had NO direct-write path at all -
        //      the only way a module's own m_UpgradeLevel could change was
        //      via the official TryModifyBlueprintModuleLevel (+1, capped
        //      by the game itself), and nothing in the UI even called that.
        //      HandleSetModuleLevel/HandleSetInventorySetModuleLevel below
        //      are new, cheat-mode-only direct writes, mirroring how
        //      HandleSetLevel already works for a whole item.
        // Blueprint/item-level itself was ALREADY an uncapped direct write
        // (HandleSetLevel has never validated against maxLevel) - the only
        // thing stopping you from typing past max there was the frontend
        // greying out the +/Upgrade Level buttons, which the client relaxes
        // once Cheat Mode is on (see EditorUI.html).
        private bool _cheatModeEnabled = false;

        private string BuildCheatModeJson() => "{\"enabled\":" + (_cheatModeEnabled ? "true" : "false") + "}";

        private void HandleSetCheatMode(HttpListenerContext ctx)
        {
            string enabledStr = ctx.Request.QueryString["enabled"];
            bool wantEnabled = string.Equals(enabledStr, "true", StringComparison.OrdinalIgnoreCase);

            bool turningOn = wantEnabled && !_cheatModeEnabled;
            _cheatModeEnabled = wantEnabled;
            Log($"HandleSetCheatMode: cheat mode <- {_cheatModeEnabled}.");

            string backupName = null;
            if (turningOn)
            {
                // Per Cameron: back up the save the moment cheat mode gets
                // switched on, before any out-of-bounds edit can happen -
                // same CreateBackup used everywhere else in this file, just
                // triggered by this instead of SaveNow()'s own once-per-
                // session auto-backup (which may have already fired earlier
                // and wouldn't fire again here).
                backupName = CreateBackup("cheat-mode-enabled");
                Log("HandleSetCheatMode: pre-cheat-mode backup " + (backupName != null ? "created (" + backupName + ")" : "FAILED - see the log line above this one"));
            }

            WriteJson(ctx, 200, "{\"ok\":true,\"enabled\":" + (_cheatModeEnabled ? "true" : "false") +
                ",\"backupName\":" + JsonStr(backupName) + "}");
        }

        private void HandleSetModuleLevel(HttpListenerContext ctx)
        {
            if (!_cheatModeEnabled) { WriteJson(ctx, 400, "{\"error\":\"Enable Cheat Mode to set a module's level directly - this bypasses the game's own upgrade cap.\"}"); return; }

            int bpIndex = QueryInt(ctx, "blueprintIndex", -1);
            int modIndex = QueryInt(ctx, "moduleIndex", -1);
            int level = QueryInt(ctx, "level", -1);
            if (level < 0) { WriteJson(ctx, 400, "{\"error\":\"missing or bad level\"}"); return; }

            var blueprints = GetBlueprintsSnapshot();
            if (bpIndex < 0 || bpIndex >= blueprints.Count) { WriteJson(ctx, 400, "{\"error\":\"bad blueprintIndex\"}"); return; }
            object bp = blueprints[bpIndex];
            object generatedData = GetInstanceMemberValue(bp, "m_GeneratedData");
            object module = GetModuleAt(generatedData, modIndex);
            if (module == null) { WriteJson(ctx, 400, "{\"error\":\"bad moduleIndex\"}"); return; }

            bool wrote = TrySetInstanceMemberValue(module, "m_UpgradeLevel", level);
            bool wroteModuleBack = wrote && TryWriteModuleBack(generatedData, modIndex, module);
            bool wroteGeneratedBack = wroteModuleBack && TrySetInstanceMemberValue(bp, "m_GeneratedData", generatedData);
            Log($"HandleSetModuleLevel: blueprint[{bpIndex}] module[{modIndex}] m_UpgradeLevel <- {level}, wroteBack={wroteGeneratedBack}.");
            if (wroteGeneratedBack) SaveNow();
            WriteJson(ctx, 200, "{\"ok\":" + (wroteGeneratedBack ? "true" : "false") + "}");
        }

        private void HandleSetInventoryModuleLevel(HttpListenerContext ctx)
        {
            if (!_cheatModeEnabled) { WriteJson(ctx, 400, "{\"error\":\"Enable Cheat Mode to set a module's level directly - this bypasses the game's own upgrade cap.\"}"); return; }

            int index = QueryInt(ctx, "index", -1);
            int modIndex = QueryInt(ctx, "moduleIndex", -1);
            int level = QueryInt(ctx, "level", -1);
            if (level < 0) { WriteJson(ctx, 400, "{\"error\":\"missing or bad level\"}"); return; }

            var items = GetInventorySnapshot();
            if (index < 0 || index >= items.Count) { WriteJson(ctx, 400, "{\"error\":\"bad index\"}"); return; }
            object item = items[index];
            object generatedData = GetInstanceMemberValue(item, "m_GeneratedData");
            object module = GetModuleAt(generatedData, modIndex);
            if (module == null) { WriteJson(ctx, 400, "{\"error\":\"bad moduleIndex\"}"); return; }

            bool wrote = TrySetInstanceMemberValue(module, "m_UpgradeLevel", level);
            bool wroteModuleBack = wrote && TryWriteModuleBack(generatedData, modIndex, module);
            bool wroteGeneratedBack = wroteModuleBack && TrySetInstanceMemberValue(item, "m_GeneratedData", generatedData);
            bool wroteBack = wroteGeneratedBack && TryWriteInventoryItemBack(index, item);
            Log($"HandleSetInventoryModuleLevel: inventory[{index}] module[{modIndex}] m_UpgradeLevel <- {level}, wroteBack={wroteBack}.");
            if (wroteBack) SaveNow();
            WriteJson(ctx, 200, "{\"ok\":" + (wroteBack ? "true" : "false") + "}");
        }

        // ---------- module type catalog (for swapping what a module slot IS) ----------

        private void RefreshModuleCandidates() { RefreshModuleCandidates(true); }

        private void RefreshModuleCandidates(bool verbose)
        {
            if (_itemModuleScriptableType == null)
                _itemModuleScriptableType = FindType("Il2CppKeepsake.HyperSpace.System.Modifiers.ItemModule.ItemModuleScriptable");
            if (_itemModuleScriptableType == null) { Log("ItemModuleScriptable type not found."); return; }

            // FindObjectsOfType reliably returns 0 for these (confirmed live,
            // even while looking straight at an item's rendered module
            // descriptions) - these scriptables just aren't tracked as "live
            // scene objects". Found the real source via the module-database
            // search: PersistentScriptableLibrary.AllItemModules is a plain
            // List<ItemModuleScriptable> - the same concrete-list shape that
            // blueprints already read perfectly - so use that instead.
            object items_source = null;
            var libType = FindType("Il2CppKeepsake.GeneratedItems.Cosmetics.PersistentScriptableLibrary");
            if (libType != null)
            {
                items_source = GetStaticMemberValue(libType, "AllItemModules");
                if (items_source == null) Log("PersistentScriptableLibrary.AllItemModules returned null (library may not be loaded yet).");
            }
            else
            {
                Log("PersistentScriptableLibrary type not found - falling back to FindObjectsOfType.");
            }

            List<object> items;
            if (items_source != null)
            {
                items = ReadIndexedCollection(items_source);
            }
            else
            {
                // Old fallback path, kept in case PersistentScriptableLibrary
                // isn't available for some reason.
                object arr = TryFindAllObjectsOfType(_itemModuleScriptableType);
                if (arr == null)
                {
                    Log("Could not enumerate loaded module types via PersistentScriptableLibrary OR FindObjectsOfType.");
                    return;
                }
                items = ReadIndexedCollection(arr);
            }

            _moduleCandidates.Clear();
            int skippedNoGuid = 0;
            foreach (var obj in items)
            {
                if (obj == null) continue;
                string guid = GetInstanceMemberValue(obj, "AssetGUID") as string;
                string name = GetInstanceMemberValue(obj, "DisplayName") as string;
                if (string.IsNullOrEmpty(name)) name = GetInstanceMemberValue(obj, "name") as string;
                if (string.IsNullOrEmpty(guid)) { skippedNoGuid++; continue; }
                var candidate = new ModuleCandidate { Guid = guid, DisplayName = name, Scriptable = obj };
                candidate.AllowedTemplateGuids = ReadAssetReferenceGuids(GetInstanceMemberValue(obj, "m_AllowedItems"));
                candidate.ForbiddenTemplateGuids = ReadAssetReferenceGuids(GetInstanceMemberValue(obj, "m_ForbiddenItems"));
                object isBasicVal = GetInstanceMemberValue(obj, "m_IsBasicModule");
                candidate.IsBasicModule = isBasicVal != null && Convert.ToBoolean(isBasicVal);
                _moduleCandidates.Add(candidate);
            }

            if (items.Count == 0)
            {
                Log("Module source read 0 items - check the log line(s) just above this for which read strategy failed.");
            }
            else if (_moduleCandidates.Count == 0)
            {
                // Got real objects but couldn't find a guid/name on any of
                // them - the field names we guessed (AssetGUID/DisplayName)
                // must be wrong for this game. Dump the first one's real shape
                // so we can see the actual field names in one round trip.
                Log($"Read {items.Count} module scriptable(s) but none had a usable AssetGUID/DisplayName - dumping the first one's real shape:");
                DumpValueShapeAndValues(items[0], "module scriptable[0]");
            }
            else if (skippedNoGuid > 0)
            {
                Log($"Loaded {_moduleCandidates.Count} module type(s) ({skippedNoGuid} skipped for missing guid/name).");
            }

            // One-time diagnostic: dump a sample module scriptable's full
            // shape so we can check for a school/category/compatible-item
            // field. GeneratedItem carries its own m_SchoolGuid (confirmed
            // different across item types in earlier dumps), which suggests
            // modules are likely grouped into families too (e.g. on-foot gun
            // modules vs ship-mounted weapon modules) - this would explain
            // seeing what look like two modules with the same/similar name.
            if (_moduleCandidates.Count > 0 && _dumpedTypeShapes.Add("ItemModuleScriptable-sample"))
            {
                Log($"One-time diagnostic: dumping full shape of a sample module scriptable to check for a school/category field.");
                DumpValueShapeAndValues(_moduleCandidates[0].Scriptable, $"sample module scriptable ({_moduleCandidates[0].DisplayName})");
            }

            SortCandidatesByName(_moduleCandidates);
            _selectedCandidateIndex = _moduleCandidates.Count > 0 ? 0 : -1;

            if (verbose)
            {
                Log($"--- {_moduleCandidates.Count} module types loaded ---");
                for (int i = 0; i < _moduleCandidates.Count; i++)
                {
                    var c = _moduleCandidates[i];
                    Log($"  [{i}] {c.DisplayName}  rarity {GetRarityRangeString(c.Scriptable)}  guid={c.Guid}");
                }
                Log("Use , / . to browse (Shift = jump by 10), Insert to swap the selected module to the browsed type.");
            }
        }

        // Loads the cosmetics catalog (scopes, color swaps, etc.) from
        // PersistentScriptableLibrary.AllCosmetics - confirmed 26 entries: 12
        // Color swaps (IsAttachment=False) and 14 Scope attachments
        // (IsAttachment=True). Every CosmeticData has its own m_SlotType, and
        // a CosmeticSelection slot can only be filled with a cosmetic whose
        // SlotType matches the slot's own m_SlotType.
        private void RefreshCosmeticCandidates()
        {
            var libType = FindType("Il2CppKeepsake.GeneratedItems.Cosmetics.PersistentScriptableLibrary");
            if (libType == null) { Log("RefreshCosmeticCandidates: PersistentScriptableLibrary type not found."); return; }

            object raw = null;
            try { raw = GetStaticMemberValue(libType, "AllCosmetics"); }
            catch (Exception ex) { Log("RefreshCosmeticCandidates: reading AllCosmetics threw: " + ex.Message); }
            if (raw == null) { Log("RefreshCosmeticCandidates: AllCosmetics returned null (library may not be loaded yet)."); return; }

            var items = ReadIndexedCollection(raw);
            _cosmeticCandidates.Clear();
            foreach (var obj in items)
            {
                if (obj == null) continue;
                string guid = GetInstanceMemberValue(obj, "m_AssetGuid") as string;
                string name = GetInstanceMemberValue(obj, "name") as string;
                if (string.IsNullOrEmpty(guid)) continue;
                object slotTypeVal = GetInstanceMemberValue(obj, "m_SlotType");
                object isAttachmentVal = SafeGet(() => obj.GetType().GetProperty("IsAttachment", BindingFlags.Public | BindingFlags.Instance)?.GetValue(obj));
                _cosmeticCandidates.Add(new CosmeticCandidate
                {
                    Guid = guid,
                    DisplayName = string.IsNullOrEmpty(name) ? guid : name,
                    SlotType = slotTypeVal?.ToString(),
                    IsAttachment = isAttachmentVal is bool b && b
                });
            }
            _cosmeticCandidates.Sort((a, c) => string.Compare(a.DisplayName, c.DisplayName, StringComparison.OrdinalIgnoreCase));
            Log($"RefreshCosmeticCandidates: loaded {_cosmeticCandidates.Count} cosmetic type(s).");
        }

        private void RefreshTemplateOriginalNames()
        {
            _templateOriginalNames.Clear();
            var libType = FindType("Il2CppKeepsake.GeneratedItems.Cosmetics.PersistentScriptableLibrary");
            if (libType == null) { Log("RefreshTemplateOriginalNames: PersistentScriptableLibrary type not found."); return; }

            try
            {
                object weaponDict = GetStaticMemberValue(libType, "m_WeaponEntriesByGuid");
                if (weaponDict != null)
                {
                    foreach (var kv in ReadIndexedCollection(weaponDict))
                    {
                        string key = GetInstanceMemberValue(kv, "Key") as string;
                        object value = GetInstanceMemberValue(kv, "Value");
                        object data = GetInstanceMemberValue(value, "m_Data");
                        string displayName = (GetInstanceMemberValue(data, "ItemDisplayText") as string)?.Trim();
                        if (!string.IsNullOrEmpty(key) && !string.IsNullOrEmpty(displayName))
                            _templateOriginalNames[key] = displayName;
                    }
                }
            }
            catch (Exception ex) { Log("RefreshTemplateOriginalNames: weapon entries threw: " + ex.Message); }

            try
            {
                object shipList = GetStaticMemberValue(libType, "AllShipComponents");
                if (shipList != null)
                {
                    foreach (var comp in ReadIndexedCollection(shipList))
                    {
                        string guid = GetInstanceMemberValue(comp, "m_AssetGUID") as string;
                        // Confirmed via a real log: ship components expose
                        // "ItemDisplayName", NOT "ItemDisplayText" like the weapon
                        // side does - this was silently returning null (and
                        // therefore contributing 0 entries) before.
                        string displayName = (GetInstanceMemberValue(comp, "ItemDisplayName") as string)?.Trim();
                        if (!string.IsNullOrEmpty(guid) && !string.IsNullOrEmpty(displayName))
                            _templateOriginalNames[guid] = displayName;
                    }
                }
            }
            catch (Exception ex) { Log("RefreshTemplateOriginalNames: ship components threw: " + ex.Message); }

            Log($"RefreshTemplateOriginalNames: loaded {_templateOriginalNames.Count} template original name(s).");
        }

        // Confirmed via "Inspect Consumable/Pickup Name Catalog":
        // CraftablesLibrary.LazyUnlockToCraftable (Dictionary<string,
        // Craftable>) is keyed by the exact same guid a non-generated
        // InventoryItem carries as its own m_GUID, and Craftable.DisplayName
        // is the real name (e.g. "Med EM-8"). This is a totally separate
        // catalog from PersistentScriptableLibrary - lives under
        // Il2CppKeepsake.GameplayFeatures.Assembler instead.
        private void RefreshCraftableNames()
        {
            _craftableNamesByGuid.Clear();
            _craftableCategoryByGuid.Clear();
            _consumableCategoryWhitelist.Clear();
            var libType = FindType("Il2CppKeepsake.GameplayFeatures.Assembler.CraftablesLibrary");
            if (libType == null) { Log("RefreshCraftableNames: CraftablesLibrary type not found."); return; }

            try
            {
                object craftableDict = GetStaticMemberValue(libType, "LazyUnlockToCraftable");
                if (craftableDict != null)
                {
                    foreach (var kv in ReadIndexedCollection(craftableDict))
                    {
                        string key = GetInstanceMemberValue(kv, "Key") as string;
                        object value = GetInstanceMemberValue(kv, "Value");
                        // Trimmed defensively: a stray leading/trailing space on
                        // either this or the weapon/ship catalog's display name
                        // would silently break the exact-string name-match in
                        // IsSwappableConsumableGuid below without showing up as
                        // a visible difference anywhere.
                        string displayName = (GetInstanceMemberValue(value, "DisplayName") as string)?.Trim();
                        if (!string.IsNullOrEmpty(key) && !string.IsNullOrEmpty(displayName))
                            _craftableNamesByGuid[key] = displayName;

                        if (!string.IsNullOrEmpty(key))
                        {
                            object category = SafeGet(() => GetInstanceMemberValue(value, "m_Category"));
                            if (category != null) _craftableCategoryByGuid[key] = category.ToString();
                        }
                    }
                }
            }
            catch (Exception ex) { Log("RefreshCraftableNames: LazyUnlockToCraftable threw: " + ex.Message); }

            // Empirically determine which category value(s) real consumables
            // actually have, using the confirmed-real guids in
            // KnownConsumableGuids, instead of guessing at enum member names
            // (see _consumableCategoryWhitelist's comment for why guessing by
            // name is unreliable here).
            foreach (var g in KnownConsumableGuids)
                if (_craftableCategoryByGuid.TryGetValue(g, out var cat)) _consumableCategoryWhitelist.Add(cat);

            var distinctCategories = new HashSet<string>(_craftableCategoryByGuid.Values);
            Log($"RefreshCraftableNames: loaded {_craftableNamesByGuid.Count} craftable name(s), {distinctCategories.Count} distinct category value(s) seen [{string.Join(", ", distinctCategories)}], consumable whitelist = [{string.Join(", ", _consumableCategoryWhitelist)}].");
        }

        // Confirmed via user feedback: real one-time expendable consumables.
        // Expendable RPG/Railgun are real CraftablesLibrary entries and this
        // override just settles their name-match against _templateOriginalNames
        // in their favor. Expendable Minigun turned out to be a different
        // situation entirely - a user-run "Inspect Consumable Filter Debug"
        // dump confirmed it isn't in CraftablesLibrary.LazyUnlockToCraftable
        // (the "Change Consumable" catalog's source) at all - it's only in
        // m_WeaponEntriesByGuid, the WEAPON catalog, alongside real guns like
        // Ironbelt LMG and SR.99 Javelin. So the actual bug wasn't a
        // misclassification, it never had a chance to show up in the first
        // place. See the _templateOriginalNames fallback added to
        // IsSwappableConsumableGuid and BuildConsumableTemplateCatalogJson
        // below, which is what actually surfaces it now.
        private static readonly HashSet<string> ConfirmedConsumableNames = new HashSet<string>(StringComparer.OrdinalIgnoreCase)
        {
            "Expendable Minigun",
            "Expendable RPG",
            "Expendable Railgun",
        };

        // Confirmed via user feedback: real equipment/weapon blueprints
        // (belong in the weapon "Base item" list) that also turned up in
        // CraftablesLibrary. The name-match against _templateOriginalNames
        // below was expected to catch these generically (they're all melee
        // weapons that should also live in m_WeaponEntriesByGuid), but user
        // testing showed it still wasn't catching Wrench even after Crowbar
        // and Heat Blade were added here - so all three are now listed
        // explicitly rather than trusting the generic match alone.
        private static readonly HashSet<string> ConfirmedBlueprintNames = new HashSet<string>(StringComparer.OrdinalIgnoreCase)
        {
            "Crowbar",
            "Heat Blade",
            "Wrench",
        };

        // Backs the "Change Consumable" combo box - the full catalog of
        // everything CraftablesLibrary.LazyUnlockToCraftable knows about, not
        // just what's currently carried, so the player can switch a slot to
        // any consumable in the game (not just ones they've already seen).
        // LazyUnlockToCraftable turned out to be a broader "craftables"
        // catalog than consumables-only - confirmed via user feedback that
        // real equipment (Wrench, same idea as the melee Heat Blade) shows up
        // in it too. Filtered in IsSwappableConsumableGuid below.
        private string BuildConsumableTemplateCatalogJson()
        {
            if (_craftableNamesByGuid.Count == 0) RefreshCraftableNames();
            if (_templateOriginalNames.Count == 0) RefreshTemplateOriginalNames();
            var sb = new StringBuilder();
            sb.Append("[");
            bool first = true;
            int skipped = 0;
            foreach (var kv in _craftableNamesByGuid)
            {
                if (!IsSwappableConsumableGuid(kv.Key)) { skipped++; continue; }
                if (!first) sb.Append(",");
                first = false;
                sb.Append("{\"guid\":").Append(JsonStr(kv.Key))
                  .Append(",\"name\":").Append(JsonStr(kv.Value))
                  .Append("}");
            }
            // A confirmed real consumable (Expendable Minigun, so far the only
            // one seen) lives in the weapon/ship catalog instead of
            // CraftablesLibrary - see ConfirmedConsumableNames' comment. Add
            // any such entries in too, same override list, skipping anything
            // already covered by the loop above (shouldn't overlap in
            // practice - the two catalogs use different guid namespaces - but
            // checked anyway).
            int addedFromTemplateCatalog = 0;
            foreach (var kv in _templateOriginalNames)
            {
                if (_craftableNamesByGuid.ContainsKey(kv.Key)) continue;
                if (!ConfirmedConsumableNames.Contains(kv.Value)) continue;
                if (!first) sb.Append(",");
                first = false;
                sb.Append("{\"guid\":").Append(JsonStr(kv.Key))
                  .Append(",\"name\":").Append(JsonStr(kv.Value))
                  .Append("}");
                addedFromTemplateCatalog++;
            }
            sb.Append("]");
            Log($"BuildConsumableTemplateCatalogJson: {_craftableNamesByGuid.Count - skipped + addedFromTemplateCatalog} shown ({addedFromTemplateCatalog} from the weapon/ship catalog), {skipped} filtered out as non-consumable.");
            return sb.ToString();
        }

        // Shared gate for both the catalog builder above and
        // HandleSwapConsumable, so a client can't bypass the frontend filter
        // by calling the swap endpoint directly with a non-consumable guid.
        // Layered, most-trusted-signal-first:
        //   1. ConfirmedConsumableNames always wins (explicit user-confirmed
        //      real consumables, even ones that share part of their name with
        //      unrelated equipment elsewhere).
        //   2. ConfirmedBlueprintNames always hides (explicit user-confirmed
        //      equipment that showed up in the craftables catalog, same idea
        //      as Wrench).
        //   3. Otherwise, hide it if its name matches a KNOWN blueprint/
        //      equipment name - _templateOriginalNames is populated from
        //      m_WeaponEntriesByGuid + AllShipComponents (every on-foot
        //      weapon and ship component the game has), so this generically
        //      catches most equipment without needing a hardcoded list.
        //      Case-insensitive: the weapon catalog's ItemDisplayText and the
        //      craftables catalog's DisplayName aren't guaranteed to agree on
        //      capitalization for the same real item.
        //   4. Otherwise, fall back to the softer category-whitelist heuristic
        //      (_consumableCategoryWhitelist) for anything none of the above
        //      knows about.
        //   5. If the guid isn't in CraftablesLibrary at all, it's normally
        //      not swappable - EXCEPT the ConfirmedConsumableNames entries
        //      that turned out to live in the weapon/ship catalog instead
        //      (Expendable Minigun). Kept as its own final check rather than
        //      folded into step 1 so nothing else from that much bigger
        //      catalog can slip through on a name coincidence.
        private bool IsSwappableConsumableGuid(string guid)
        {
            if (string.IsNullOrEmpty(guid)) return false;
            if (_craftableNamesByGuid.TryGetValue(guid, out var name))
            {
                if (ConfirmedConsumableNames.Contains(name)) return true;
                if (ConfirmedBlueprintNames.Contains(name)) return false;
                var knownBlueprintNames = new HashSet<string>(_templateOriginalNames.Values, StringComparer.OrdinalIgnoreCase);
                if (knownBlueprintNames.Contains(name)) return false;
                if (_consumableCategoryWhitelist.Count == 0) return true; // no signal to filter on - don't guess-exclude
                if (!_craftableCategoryByGuid.TryGetValue(guid, out var category)) return true; // category unreadable - don't guess-exclude
                return _consumableCategoryWhitelist.Contains(category);
            }
            if (_templateOriginalNames.TryGetValue(guid, out var templateName) && ConfirmedConsumableNames.Contains(templateName)) return true;
            return false;
        }

        // m_WeaponEntriesByGuid turned out NOT to be exclusively combat
        // weapons despite the earlier assumption (see the comment below where
        // it's read) - confirmed by the user seeing on-foot TOOLS (Multi
        // Tool, Mining Laser) and Minigun mixed in among actual guns when
        // browsing the "Change Base Item" list for a Weapons-category
        // blueprint. There's no separate per-entry category field on
        // WeaponEntry to key off of (unlike ship components' m_typeOfItem),
        // so this is a plain name blocklist built from what's actually been
        // seen - if another non-weapon turns up in the list, add its exact
        // display name here.
        // "Multi-tool" corrected from "Multi Tool" (space) - a real
        // "Inspect Consumable Filter Debug" dump showed the game's actual
        // string uses a hyphen, which OrdinalIgnoreCase doesn't paper over
        // (it only ignores case, not punctuation), so the space version was
        // silently never matching and Multi-tool was leaking into the
        // Weapons base-item list uncaught.
        // "Expendable Minigun" added per user feedback - it's a real
        // consumable (see ConfirmedConsumableNames), not a selectable base
        // weapon, even though it lives in this same weapon-entries dict.
        private static readonly HashSet<string> NonWeaponToolNames = new HashSet<string>(StringComparer.OrdinalIgnoreCase)
        {
            "Multi-tool",
            "Mining Laser",
            "Minigun",
            "Expendable Minigun",
        };

        // Static guid -> (category, display name) reference table, sourced
        // from JumpSaves (github.com/gurudennis/JumpSaves, MIT licensed), an
        // independent offline Jump Space save editor that reverse-engineered
        // the full 40-item static MajorItemType catalog directly from the
        // game's own asset guids (JSL/Constants.cs). Every "Raw" guid there
        // is a plain 32-char Unity asset guid with no dashes - the same
        // format m_AssetGUID/m_WeaponEntriesByGuid keys come back as from
        // live reflection, so these line up directly once both sides are
        // normalized (lowercased, dashes stripped - see NormalizeGuid).
        // This exists specifically to fill in the ship-component category
        // gap noted above (AllShipComponents entries have no per-entry
        // category signal of their own yet) and to guarantee the full 40
        // template catalog is present even if live discovery ever misses an
        // entry.
        private static string NormalizeGuid(string guid)
        {
            if (string.IsNullOrEmpty(guid)) return null;
            return guid.Replace("-", "").ToLowerInvariant();
        }

        private static readonly Dictionary<string, string> StaticItemCategoryByGuid = new Dictionary<string, string>
        {
            // Player Weapons (on-foot)
            { "b5b14acbf52842b4f90002bd4e9d1391", "Weapons" }, // Bulldog-SA7 (AR)
            { "dd2afc39b34322c4381b6a3ed3e5988a", "Weapons" }, // VSR Halberd (AR)
            { "b90b477e483f6cc4aa9a48f33e4400e3", "Weapons" }, // Stinger MP-75 (SMG)
            { "ea1f1e6ac3c88fe469708ce10b5e451a", "Weapons" }, // CX-305 Sideclip (SMG)
            { "11d2d7e9f079ed4499c9591d8d68c7a7", "Weapons" }, // MAW-23 (Shotgun)
            { "2cbd789d647fa9a4d96f462001a99c91", "Weapons" }, // SR.99 Javelin (Sniper)
            { "55b2b5f6d20d4eb4ab9ef216e5237928", "Weapons" }, // Ironbelt (LMG)
            { "046383b13f53ad144805f5dca98b4b86", "Weapons" }, // Heat Blade (Melee)
            { "a52219e07db611248800766fe8d53744", "Weapons" }, // Wrench (Melee)
            { "f077b42a85cfb7f4bb0d55729c4fc5c0", "Weapons" }, // Crowbar (Melee)
            // Multiturrets
            { "558ac570efdfbe64390ab32c39d45ff3", "Multiturrets" }, // Assault Turrets
            { "e2b646f5b39d9994a929c62d32635793", "Multiturrets" }, // Mining Lasers
            { "b98c1f15ee8b58343acf4f62ddaa93ab", "Multiturrets" }, // Flak Launcher Turrets
            { "5e4082467be3c344698f724e74c6660a", "Multiturrets" }, // Gatling Turrets
            // Pilot Cannons
            { "c7e0f6d13e18db440b37a42470f42744", "Pilot Cannons" }, // Fragmentation Cannon
            { "8c32f9e4ff293894582ceb6b831c40af", "Pilot Cannons" }, // Reaver Rotary Cannon
            { "d151b8914ed56d74985d345a118f9a5e", "Pilot Cannons" }, // Bolt Accelerator
            { "c3346b9a547672948a2fe02ea2bb5de5", "Pilot Cannons" }, // Disruptor Laser
            // Special Weapons
            { "e1d2c08495890004e9ebb0ca7fe7c5a1", "Special Weapons" }, // Burst Shield
            { "3290a7dbea83de5488cca77e44cae0a8", "Special Weapons" }, // Vulcan Rotary Cannon
            { "889c471a3fab57d44b28f2592be5d7f8", "Special Weapons" }, // Thunderburst Heavy Cannon
            { "d593e671947518544ab6dcd2deef3e2e", "Special Weapons" }, // Lance Railgun
            { "15bebeb1e9273af4fb7f4213452a6c58", "Special Weapons" }, // Missile Launcher
            { "10b36cf783993154cbcf8679744cd900", "Special Weapons" }, // Targeting Module
            // Engines
            { "f1302af5a63e825478b7fb9f953401aa", "Engines" }, // Drift Phase Engine
            { "fb2bbc3f13c228a44ba53f020e1df249", "Engines" }, // Nitro Pulse Engine
            { "dde01f5723d9b0047abb3d223f5541cd", "Engines" }, // Mass Ejector Engine
            { "4524f4ac1fa8cb34dbff50f8c5c14927", "Engines" }, // Microplasma Engine
            // Shield Generators
            { "352d8b4d1f0f38249b5a88c19a11caf3", "Shield Generators" }, // Skirmisher Shield
            { "554d65de54698714c9f5d2f73bc33261", "Shield Generators" }, // Fighter Shield
            { "7a2d7e2dbbb33f742a1c885667377425", "Shield Generators" }, // Fortress Shield
            // Sensors
            { "3ee2f96ed55e8de4898d4f922eba8f66", "Sensors" }, // Sector Scanner
            { "eac8acd058989964ab7a07cf7de03fa5", "Sensors" }, // Supply Uplink Unit
            { "d4b4eb9b7856fce4e9c1bb3a78c9807e", "Sensors" }, // Vector Targeting Module
            // Reactors
            { "95c51a0f21d28ba459a43bbf3dbc0790", "Reactors" }, // Null Wave Reactor
            { "65e495611fd9233419832053f8ce55bd", "Reactors" }, // Split Reactor
            { "f400f9acd1731b64a87b69ce40517971", "Reactors" }, // Materia Scatter Reactor
            { "85b241f7f2fa6654e9c522519358d1bc", "Reactors" }, // Solid State Reactor
            // Aux. Generators
            { "2c60b00a88d34b546865a36738fabc2a", "Aux. Generators" }, // Bio Fission Generator
            { "4bfcb457279ce824e8fd7989760d9252", "Aux. Generators" }, // Materia Shift Generator
            { "8cbe912f6e885134680a52935cca96a5", "Aux. Generators" }, // Null Tension Generator
        };

        private static readonly Dictionary<string, string> StaticItemNameByGuid = new Dictionary<string, string>
        {
            { "b5b14acbf52842b4f90002bd4e9d1391", "Bulldog-SA7 (AR)" },
            { "dd2afc39b34322c4381b6a3ed3e5988a", "VSR Halberd (AR)" },
            { "b90b477e483f6cc4aa9a48f33e4400e3", "Stinger MP-75 (SMG)" },
            { "ea1f1e6ac3c88fe469708ce10b5e451a", "CX-305 Sideclip (SMG)" },
            { "11d2d7e9f079ed4499c9591d8d68c7a7", "MAW-23 (Shotgun)" },
            { "2cbd789d647fa9a4d96f462001a99c91", "SR.99 Javelin (Sniper)" },
            { "55b2b5f6d20d4eb4ab9ef216e5237928", "Ironbelt (LMG)" },
            { "046383b13f53ad144805f5dca98b4b86", "Heat Blade (Melee)" },
            { "a52219e07db611248800766fe8d53744", "Wrench (Melee)" },
            { "f077b42a85cfb7f4bb0d55729c4fc5c0", "Crowbar (Melee)" },
            { "558ac570efdfbe64390ab32c39d45ff3", "Assault Turrets" },
            { "e2b646f5b39d9994a929c62d32635793", "Mining Lasers" },
            { "b98c1f15ee8b58343acf4f62ddaa93ab", "Flak Launcher Turrets" },
            { "5e4082467be3c344698f724e74c6660a", "Gatling Turrets" },
            { "c7e0f6d13e18db440b37a42470f42744", "Fragmentation Cannon" },
            { "8c32f9e4ff293894582ceb6b831c40af", "Reaver Rotary Cannon" },
            { "d151b8914ed56d74985d345a118f9a5e", "Bolt Accelerator" },
            { "c3346b9a547672948a2fe02ea2bb5de5", "Disruptor Laser" },
            { "e1d2c08495890004e9ebb0ca7fe7c5a1", "Burst Shield" },
            { "3290a7dbea83de5488cca77e44cae0a8", "Vulcan Rotary Cannon" },
            { "889c471a3fab57d44b28f2592be5d7f8", "Thunderburst Heavy Cannon" },
            { "d593e671947518544ab6dcd2deef3e2e", "Lance Railgun" },
            { "15bebeb1e9273af4fb7f4213452a6c58", "Missile Launcher" },
            { "10b36cf783993154cbcf8679744cd900", "Targeting Module" },
            { "f1302af5a63e825478b7fb9f953401aa", "Drift Phase Engine" },
            { "fb2bbc3f13c228a44ba53f020e1df249", "Nitro Pulse Engine" },
            { "dde01f5723d9b0047abb3d223f5541cd", "Mass Ejector Engine" },
            { "4524f4ac1fa8cb34dbff50f8c5c14927", "Microplasma Engine" },
            { "352d8b4d1f0f38249b5a88c19a11caf3", "Skirmisher Shield" },
            { "554d65de54698714c9f5d2f73bc33261", "Fighter Shield" },
            { "7a2d7e2dbbb33f742a1c885667377425", "Fortress Shield" },
            { "3ee2f96ed55e8de4898d4f922eba8f66", "Sector Scanner" },
            { "eac8acd058989964ab7a07cf7de03fa5", "Supply Uplink Unit" },
            { "d4b4eb9b7856fce4e9c1bb3a78c9807e", "Vector Targeting Module" },
            { "95c51a0f21d28ba459a43bbf3dbc0790", "Null Wave Reactor" },
            { "65e495611fd9233419832053f8ce55bd", "Split Reactor" },
            { "f400f9acd1731b64a87b69ce40517971", "Materia Scatter Reactor" },
            { "85b241f7f2fa6654e9c522519358d1bc", "Solid State Reactor" },
            { "2c60b00a88d34b546865a36738fabc2a", "Bio Fission Generator" },
            { "4bfcb457279ce824e8fd7989760d9252", "Materia Shift Generator" },
            { "8cbe912f6e885134680a52935cca96a5", "Null Tension Generator" },
        };

        // Static guid -> canonical module title reference table, sourced from
        // JumpSaves' ShipModuleType + PlayerWeaponModuleType catalogs
        // (JSL/Constants.cs) - 117 unique entries covering every Upgradeable
        // Feature and Custom Module the game has, for both ship components
        // and on-foot weapons. Unlike the in-game "description" text (which
        // is level/rarity-dependent flavor text pulled via
        // GetLocalizedDescription and can be vague, e.g. doesn't always spell
        // out a status effect name explicitly), these titles are the game's
        // own short, consistent, guid-keyed identifiers - e.g. guid
        // "318504b5..." is always "Sear chance on hit" no matter what
        // rarity/level the module rolled. Exposed to the client as
        // "staticTitle" alongside "description" so status-effect tagging
        // (see STATUS_EFFECT_INFO/statusEffectTagsHtml in EditorUI.html) has
        // a second, more reliable signal to match against - some module
        // guids here aren't matched by any live-discovered module yet (the
        // reflection side doesn't have a full 1:1 guid catalog of its own),
        // so this is intentionally a flat guid->title lookup rather than
        // something merged into _itemTemplateCandidates like the item table
        // above.
        private static readonly Dictionary<string, string> StaticModuleTitleByGuid = new Dictionary<string, string>
        {
            { "9009aa4df2ad3a04ba4dea5518e1d611", "(F) Reload speed" },
            { "cafc9599b386ee84a890c2c760b62f5e", "(F) Magazine size" },
            { "df5b391e9981fdd47af8f2f6e74a9fd9", "(F) Damage" },
            { "1cb68cd7f09dd6843a9ea451429e6139", "(F) Bonus damage" },
            { "8395a832a680a8741b9e61af12c72307", "(F) Fire rate" },
            { "072b30aa0e26c5c49b7c3ca156c62282", "Reduced materia cost" },
            { "bb680a7ce4769fa4396b560d36435371", "Corrosion chance on hit" },
            { "b4c71cf386f6f3a42aaf7fe311eb202c", "Additional projectiles" },
            { "09dd872497cec754bba28c7616b8810f", "Additional shot % per mag" },
            { "c70b3f3ddb76d4141bc113b651ffbfdd", "EMP chance on hit" },
            { "e60458dfaa15275469527dab6ddf9b02", "Breach chance on hit" },
            { "bf3cecfa0702aa04e95d109144f21ed1", "Corrosion projectile" },
            { "fc4cf93ada70dcf4c910cad5faa5c9a9", "Chance to chain enemies" },
            { "6a8561321dfb64d4789ae84a0cda11d4", "Increase Rupture damage" },
            { "3fd4cd1ef685c464bab96af82388c2ac", "Breach causes Rupture" },
            { "72a1c39fe91bdee4da863bee2afa6db8", "Virus chance on hit" },
            { "5c15051e787622d43bae554502e4a052", "Virus causes EMP" },
            { "2f006f1878bb9ed4992f73cf87ac953d", "Max speed" },
            { "b9d81f3aea38f3d47848701fcbdd521b", "Max boost" },
            { "7aa83416608d90e41b0c0ecfab3e869a", "Turn rate" },
            { "782a431317dc9a64f90e4c20edfe0e04", "Acceleration" },
            { "8dacbec9a6bac2947ab3eaecb8a020f5", "Faster shield recharge" },
            { "76dc2ea8251eafe4b9752f33a15f90df", "Lower shield break chance" },
            { "34f7c993f959fbe459777c90eab95189", "Shorter shield downtime" },
            { "987886742b6da2740b8f64922c59b0b1", "Reactor capacity" },
            { "fe1243281c445474da91a86cd378d640", "Additional shots per mag" },
            { "318504b5400b90d4c81cc63c64baf0ac", "Sear chance on hit" },
            { "e8ca44d9362a2e143917f65180369a6d", "Rupture projectile" },
            { "66ad1d1ada3da75479cef1a83a739aae", "Radiation after corrosion" },
            { "64c441c7ba5afa04c86e656d35cddfd3", "Corrosion after EMP" },
            { "1a0f06c6024f86d48bdc56076def5dd3", "Shield capacity" },
            { "682de849168890a43bd79f0473a0e76b", "Virus spreads on kill" },
            { "2db0439951d75ba4dade764bbcdd1369", "Radiation projectile" },
            { "32a8f3dc569318142be2483792227bc1", "Breach after sear" },
            { "f59d3b957056095468442df700fb5a08", "Increase sear damage" },
            { "b0c37c92a2ca2f4418bd366fc1717911", "Damage after EMP" },
            { "52e9347eefe773444bc3a1520f4221af", "Reload speed" },
            { "c364f658905ff554dbda3ba3aa5bb34f", "Damage per status effect" },
            { "0858882df0957284780955d88b67f44c", "Damage after Sear" },
            { "44a3739d1453d884cad555454d1dd242", "Sear projectile" },
            { "0f8329280d1551a4981a1bab85732db7", "Corrosion after Sear" },
            { "a12a873fd77ff6c45bb949d78d06240b", "Sear after Rupture" },
            { "704bdac3db82ade45ad1690916d7ad1b", "Hits on EMP restore shield" },
            { "594cfedb80c49f548be209204da1eed6", "Disruption after EMP (1)" },
            { "a5331df01eb1f1147b27f8cb852c82ca", "Disruption after EMP (2)" },
            { "8fecf9fa19f5d0748bc7e5794d2e2e93", "(F) Damage" },
            { "bb21cfa6fd5a9364c99ef22d8d4ea38f", "(F) Fire rate" },
            { "68fbcdf863d097c498e0ffb0ec1d4cba", "(F) Magazine capacity" },
            { "2a17d7fe09ea50a47b88336247b9c5ff", "(F) Bonus magazine capacity" },
            { "13cec6085efd0a342a6ecfef9f5aa2da", "(F) Reload speed" },
            { "e755854780143a1419bec0445b46f072", "Reload speed" },
            { "425315a74cef11542b1c3fcb07d8d934", "Mag size but less damage" },
            { "676bc98f5878db4409a11c68b7e2bd59", "Consecutive crit damage" },
            { "5ef2583dd770e944e84c8ab47e12b50f", "Chance to chain enemies" },
            { "c2e9a86756b9729478c43f18a341c2e2", "Breach chance on hit" },
            { "87320adbde1d5a6448effd71fcba76b3", "Crits return ammo" },
            { "3d864ddf5a372664ebcad63c686b0ceb", "Rupture after damage" },
            { "4e049bf738976824ebdfd81f9fd34796", "Damage but lower fire rate" },
            { "4ec6f7c2d7fa7734792a2db069c46d9c", "Damage but lower mag size" },
            { "749c007fa80faf840ade9af6e8d7584f", "EMP on crit" },
            { "15748cbe448ab444c990e086e31fea7b", "Rupture chance on hit" },
            { "71a93d1d5c620864c93e796b0218a90b", "Kills restore health" },
            { "3ad789a04e7a05e42affc0e22f0a309a", "Corrosion chance on hit" },
            { "f893ca79dbff4b448bdf21715d8e6d1d", "Additional projectiles" },
            { "4ab19bf28b038444d904a1032d398ac7", "Damage" },
            { "490125f0fc44ef04090900b7eaaafeec", "Last shot does more damage" },
            { "989e818fc6f5c4a47ac1dbd682f96e94", "Magazine size" },
            { "61121570f54f3904b9bef6f39801d39c", "Final shot frag" },
            { "55561444a0d58ff4a980836c77f1905c", "Sear chance on hit nearby" },
            { "dfb61796e77bac246b8cb6786ef49297", "Sear after damage" },
            { "3c3ea2f8998b5474d91965dea056b2ac", "Kills increase melee" },
            { "767a4ec9ef9c7cf40be160743b4e6cf3", "Fire rate" },
            { "e41e01652b2bcc5479b2742f0e062ba6", "Corrosion after damage" },
            { "284e8453cfde3ee40b5316f7cf4ade45", "Damage after corrosion" },
            { "17064961c8b22fb40a445885cf78adbe", "Sear chance on hit" },
            { "bbcd941bbc8563748afe7dc0bad13e96", "Damage after EMP" },
            { "57f9ebc23ef4bbc4aa9be052158b6f63", "Damage per status effect" },
            { "44d9c736d6730d2409de0f0051e08c70", "Melee EMP after deflect" },
            { "6da7dc2db0f033242a5b6990bae55e15", "Melee heals after deflect" },
            { "e8b4433b1b4cf5648b5a7c236fdf4507", "Last shot does % more damage" },
            { "f004308cf75411f4897f0286397ca2c2", "Random status effect on hit" },
            { "a51a20461ffa1bc489e60f410939e291", "Additional shot but less damage" },
            { "037a3e370b2d3b44a9a51e125e188bf3", "Sear nearby on reload" },
            { "7968a14bbe8c617449c77d016a5ea8d0", "Kills increase speed" },
            { "a313d5434c4944a4db9e07880bdba5aa", "Melee after kill does EMP" },
            { "12c40352320ea444f9c77a71395b08aa", "Magazine size percent" },
            { "589234c5148491b4aaf3a5507f66516d", "Breach causes pierce" },
            { "ebf495b7db87dc34095f80c4fd0bea12", "Damage if rupture pool full" },
            { "e4e5defdb4de7aa41ac619e93975122b", "EMP chance on hit" },
            { "8990c7ff4b2a1a34cac6b37f53e53055", "Parry increases speed" },
            { "7b2a61372446d15499ae0f69327ceb83", "Hits on breach return ammo" },
            { "5c66eb6f47c008349a8b49f84e2e2082", "Increase speed" },
            { "d26c525617760824f8227086dd3d96a2", "Hits on Virus restore health" },
            { "b4e2f2222eb9d434885137e1bf8ccfd0", "Damage after Virus" },
            { "9d86d4d33ad602d4aa60423ffce533ce", "Corrosion spreads on kill" },
            { "92aa6c968e8654f4bada9f3ef80b1640", "Melee Corrosion after deflect" },
            { "b3770c83f3075a446803fa24b8985510", "Melee damage after deflect" },
            { "3a7e482e13b43c34997f26b5c2919733", "Breach if Rupture pool full" },
            { "97113ea8e3a5b2a44a86b82d09fe836d", "Damage causes Virus" },
            { "ce3dc6eae836c7744a841123d95dfc18", "Radiation on crit" },
            { "d766bd983a8afd941a5684e0c251aa0e", "Damage after Sear" },
            { "01e31fd07b981f04aa2f1dd074b76054", "Virus spreads on kill" },
            { "139ad3ab83c9d54408630df4b97f9f44", "Melee Virus after deflect" },
            { "bb60b003dfc8fed4e9737d0a3ba8268b", "Melee Sear after deflect" },
            { "38382857f879220468fcbaceb56e6fda", "Sear while burning" },
            { "a12c412c1a390ac4493cfda03b175993", "Sear spreads on kill" },
            { "d4ed62e9c08e23f46ad535e356990af4", "Hits on EMP restore shield" },
            { "440c9c4e30c1abd43bc5b67832bc5745", "Radiation chance on hit" },
            { "f4703aefe41a81541a3328bcb0583567", "EMP after corrosion" },
            { "5478a45dbd9c0b7428ec597f0531619e", "Melee Breach after deflect" },
            { "9f1db6fbb63757a48ad3d0a98d94286d", "Melee Rupture after deflect" },
            { "268f2baa7d7a5e449bae9eba401b5fcc", "Virus chance on hit" },
            { "e1af7dcc04bf7994e8f37f4043a56733", "Crit damage" },
            { "48734eef325405640b5c7602305b0aa6", "Virus spreads statuses on kill" },
            { "4ce8ab4b7c0cc94498d825166f9cbbfb", "Virus strengthens statuses" },
            { "2230c9a581041174c90d8ca3546ad1ad", "Fire rate ramps up" },
            { "1758c4f911d6d964cad36a998c5d0e22", "Corrosion after EMP" },
        };

        // Looks up a module's canonical static title by guid (see
        // StaticModuleTitleByGuid above). Returns null for a guid the table
        // doesn't recognize - callers should fall back to the live
        // description in that case, not treat null as an error.
        private static string TryGetStaticModuleTitle(string moduleGuid)
        {
            string title;
            if (StaticModuleTitleByGuid.TryGetValue(NormalizeGuid(moduleGuid), out title)) return title;
            return null;
        }

        private void RefreshItemTemplateCatalog()
        {
            _itemTemplateCandidates.Clear();
            var libType = FindType("Il2CppKeepsake.GeneratedItems.Cosmetics.PersistentScriptableLibrary");
            if (libType == null) { Log("RefreshItemTemplateCatalog: PersistentScriptableLibrary type not found."); return; }

            int weaponCount = 0, toolsSkipped = 0;
            try
            {
                object weaponDict = GetStaticMemberValue(libType, "m_WeaponEntriesByGuid");
                if (weaponDict != null)
                {
                    foreach (var kv in ReadIndexedCollection(weaponDict))
                    {
                        string key = GetInstanceMemberValue(kv, "Key") as string;
                        object value = GetInstanceMemberValue(kv, "Value");
                        object data = GetInstanceMemberValue(value, "m_Data");
                        string displayName = GetInstanceMemberValue(data, "ItemDisplayText") as string;
                        string typeName = null;
                        try { typeName = data == null ? null : data.GetType().Name; } catch { }
                        if (!string.IsNullOrEmpty(key) && !string.IsNullOrEmpty(displayName))
                        {
                            if (NonWeaponToolNames.Contains(displayName)) { toolsSkipped++; continue; }
                            // Every remaining entry here is safely "Weapons" -
                            // see NonWeaponToolNames above for what's excluded
                            // and why.
                            _itemTemplateCandidates.Add(new ItemTemplateCandidate { Guid = key, DisplayName = displayName, Category = "Weapons", TypeName = typeName });
                            weaponCount++;
                        }
                    }
                }
            }
            catch (Exception ex) { Log("RefreshItemTemplateCatalog: weapon entries threw: " + ex.Message); }

            int shipCount = 0;
            try
            {
                object shipList = GetStaticMemberValue(libType, "AllShipComponents");
                if (shipList != null)
                {
                    foreach (var comp in ReadIndexedCollection(shipList))
                    {
                        string guid = GetInstanceMemberValue(comp, "m_AssetGUID") as string;
                        // Confirmed via a real log: "ItemDisplayName", not
                        // "ItemDisplayText" - ship components read as a totally
                        // different property name than the weapon side.
                        string displayName = GetInstanceMemberValue(comp, "ItemDisplayName") as string;
                        // m_typeOfItem (ItemType enum, e.g. "AUXPower" - confirmed
                        // on real Aux Generator entries) looks like the real
                        // per-entry category signal, but only one category's
                        // worth of samples has been seen so far - not confident
                        // enough yet to build the enum->category table off, so
                        // this rides along as TypeName purely for the "Inspect
                        // Weapon/Ship Template Catalog" dump to confirm the rest.
                        string typeName = GetInstanceMemberValue(comp, "m_typeOfItem")?.ToString();
                        if (!string.IsNullOrEmpty(guid) && !string.IsNullOrEmpty(displayName))
                        {
                            // Category used to be left null here (no confirmed
                            // per-entry category signal from live discovery) -
                            // now backed by StaticItemCategoryByGuid, a
                            // guid->category table sourced from JumpSaves (see
                            // the comment above that dictionary). Falls back to
                            // null (fail closed) only for a guid that table
                            // doesn't recognize.
                            string category = null;
                            StaticItemCategoryByGuid.TryGetValue(NormalizeGuid(guid), out category);
                            _itemTemplateCandidates.Add(new ItemTemplateCandidate { Guid = guid, DisplayName = displayName, Category = category, TypeName = typeName });
                            shipCount++;
                        }
                    }
                }
            }
            catch (Exception ex) { Log("RefreshItemTemplateCatalog: ship components threw: " + ex.Message); }

            // Crowbar/Heat Blade/Wrench are confirmed real equipment
            // blueprints (per ConfirmedBlueprintNames) that live in
            // CraftablesLibrary instead of m_WeaponEntriesByGuid, unlike
            // every other weapon - same "wrong catalog" situation as
            // Expendable Minigun, just in the opposite direction. Without
            // this they can never appear as a selectable "Base item" even
            // though that's specifically where the user wants them.
            int mergedFromCraftables = 0;
            if (_craftableNamesByGuid.Count == 0) RefreshCraftableNames();
            foreach (var kv in _craftableNamesByGuid)
            {
                if (!ConfirmedBlueprintNames.Contains(kv.Value)) continue;
                if (_itemTemplateCandidates.Exists(c => c.Guid == kv.Key)) continue; // already present, don't duplicate
                _itemTemplateCandidates.Add(new ItemTemplateCandidate { Guid = kv.Key, DisplayName = kv.Value, Category = "Weapons", TypeName = "Craftable" });
                mergedFromCraftables++;
            }

            // Belt-and-suspenders completeness pass: guarantee every one of
            // the 40 confirmed static templates (StaticItemCategoryByGuid /
            // StaticItemNameByGuid, sourced from JumpSaves) shows up in the
            // catalog even if live discovery missed it for some reason (e.g.
            // an empty AllShipComponents on a given game version, or a guid
            // formatting mismatch upstream). Matches on normalized guid so it
            // never duplicates an entry already found live.
            int mergedFromStaticCatalog = 0;
            foreach (var kv in StaticItemNameByGuid)
            {
                string normalizedGuid = kv.Key; // StaticItemNameByGuid keys are already normalized
                if (_itemTemplateCandidates.Exists(c => NormalizeGuid(c.Guid) == normalizedGuid)) continue; // already present, don't duplicate
                string category = null;
                StaticItemCategoryByGuid.TryGetValue(normalizedGuid, out category);
                _itemTemplateCandidates.Add(new ItemTemplateCandidate { Guid = normalizedGuid, DisplayName = kv.Value, Category = category, TypeName = "StaticCatalog" });
                mergedFromStaticCatalog++;
            }

            Log($"RefreshItemTemplateCatalog: loaded {weaponCount} weapon template(s) (categorized), skipped {toolsSkipped} non-weapon tool(s) (NonWeaponToolNames), + {shipCount} ship component template(s) (categorized via StaticItemCategoryByGuid), + {mergedFromCraftables} merged in from CraftablesLibrary (ConfirmedBlueprintNames), + {mergedFromStaticCatalog} merged in from the static JumpSaves catalog (entries live discovery didn't find).");
        }

        private string BuildItemTemplateCatalogJson()
        {
            if (_itemTemplateCandidates.Count == 0) RefreshItemTemplateCatalog();
            var sb = new StringBuilder();
            sb.Append("[");
            for (int i = 0; i < _itemTemplateCandidates.Count; i++)
            {
                if (i > 0) sb.Append(",");
                var c = _itemTemplateCandidates[i];
                sb.Append("{\"guid\":").Append(JsonStr(c.Guid))
                  .Append(",\"name\":").Append(JsonStr(c.DisplayName))
                  .Append(",\"category\":").Append(JsonStr(c.Category))
                  .Append(",\"typeName\":").Append(JsonStr(c.TypeName))
                  .Append("}");
            }
            sb.Append("]");
            return sb.ToString();
        }

        // Tries several (declaring type, method name) combinations, in order of
        // preference, since this game strips engine API surface it never calls
        // itself (confirmed: UnityEngine.Resources isn't present at all here,
        // presumably because it uses Addressables instead of Resources.Load).
        private object TryFindAllObjectsOfType(Type targetType)
        {
            string[] declaringTypeNames = { "UnityEngine.Object", "UnityEngine.Resources" };
            string[] methodNames = { "FindObjectsOfType", "FindObjectsOfTypeAll" };

            foreach (var declaringTypeName in declaringTypeNames)
            {
                Type declaringType = FindType(declaringTypeName);
                if (declaringType == null)
                {
                    Log($"{declaringTypeName} not found in loaded assemblies.");
                    continue;
                }

                foreach (var methodName in methodNames)
                {
                    MethodInfo method = null;
                    foreach (var m in declaringType.GetMethods(BindingFlags.Public | BindingFlags.Static))
                    {
                        if (m.Name == methodName && m.GetParameters().Length == 1)
                        {
                            method = m;
                            break;
                        }
                    }
                    if (method == null) continue;

                    var paramType = method.GetParameters()[0].ParameterType;
                    object typeArg = paramType == typeof(Type) ? (object)targetType : Il2CppType.From(targetType);

                    try
                    {
                        object result = method.Invoke(null, new object[] { typeArg });
                        if (result != null)
                        {
                            Log($"Found module types via {declaringTypeName}.{methodName}.");
                            return result;
                        }
                    }
                    catch (Exception ex)
                    {
                        Log($"{declaringTypeName}.{methodName} failed: {ex.Message}");
                    }
                }
            }
            return null;
        }

        // FindObjectsOfType(Type) hands back an array whose C# element type is
        // the base UnityEngine.Object, not the derived type that was asked
        // for - confirmed via a real log where DumpValueShapeAndValues on a
        // matched PlayerPickupableItemHandler instance printed only
        // UnityEngine.Object's own base members (name/hideFlags/etc.), and
        // GetInstanceMemberValue(inst, "PickedUpItems") came back null, even
        // though PickedUpItems is a real confirmed property on that type -
        // because obj.GetType() (which every reflection helper here keys
        // off) reports UnityEngine.Object for these instances, not the true
        // runtime class. Every Il2Cpp interop object exposes a generic
        // TryCast<T>() instance method (visible in its own base method dump)
        // that reinterprets the same native pointer as a different wrapper
        // type - this calls that reflectively so obj.GetType() reports the
        // real type afterward and member lookups actually find the derived
        // class's members. Returns the original object unchanged if the cast
        // isn't needed or doesn't succeed (never throws).
        private object TryCastToType(object obj, Type targetType)
        {
            if (obj == null || targetType == null) return obj;
            if (targetType.IsInstanceOfType(obj)) return obj;
            try
            {
                MethodInfo genericTryCast = null;
                foreach (var m in obj.GetType().GetMethods(BindingFlags.Public | BindingFlags.Instance))
                {
                    if (m.Name == "TryCast" && m.IsGenericMethodDefinition && m.GetParameters().Length == 0)
                    {
                        genericTryCast = m;
                        break;
                    }
                }
                if (genericTryCast == null) return obj;
                object cast = genericTryCast.MakeGenericMethod(targetType).Invoke(obj, null);
                return cast ?? obj;
            }
            catch (Exception ex)
            {
                Log($"TryCastToType({targetType.FullName}) threw: {ex.InnerException?.Message ?? ex.Message}");
                return obj;
            }
        }

        private static void SortCandidatesByName(List<ModuleCandidate> list)
        {
            for (int i = 1; i < list.Count; i++)
            {
                var key = list[i];
                int j = i - 1;
                while (j >= 0 && string.Compare(list[j].DisplayName, key.DisplayName, StringComparison.OrdinalIgnoreCase) > 0)
                {
                    list[j + 1] = list[j];
                    j--;
                }
                list[j + 1] = key;
            }
        }

        private void MoveCandidateSelection(int delta)
        {
            // Used to require pressing F12 first - that keybind was removed
            // (no debug/dump actions live on an F-key anymore), so this now
            // lazily loads the catalog itself the same way the web UI does.
            if (_moduleCandidates.Count == 0) RefreshModuleCandidates(false);
            if (_moduleCandidates.Count == 0) { Log("No module types loaded - open the web UI once this session, or check the MelonLoader console for why the catalog came back empty."); return; }
            _selectedCandidateIndex = Wrap(_selectedCandidateIndex + delta, _moduleCandidates.Count);
            var c = _moduleCandidates[_selectedCandidateIndex];
            Log($"Browsing [{_selectedCandidateIndex}/{_moduleCandidates.Count - 1}] {c.DisplayName}  rarity {GetRarityRangeString(c.Scriptable)}  guid={c.Guid}");
        }

        private string GetRarityRangeString(object scriptable)
        {
            object min = GetInstanceMemberValue(scriptable, "m_MinRarity");
            object max = GetInstanceMemberValue(scriptable, "m_MaxRarity");
            return $"{min}-{max}";
        }

        // Confirmed via a real dump of ItemModuleScriptable (see "One-time
        // diagnostic: dumping full shape of a sample module scriptable"):
        // the max level a module can reach isn't a single constant, it's
        // per-rarity - four separate properties, m_MaxUpgradeLevel_Common /
        // _Rare / _Epic / _Legendary (the sample module had all four = 5, but
        // there's no reason to assume every module does). Reads whichever one
        // matches the module's CURRENT rarity, since that's what's actually
        // relevant to show next to its current level.
        private int GetModuleMaxLevel(object scriptable, object rarity)
        {
            if (scriptable == null || rarity == null) return -1;
            object val = GetInstanceMemberValue(scriptable, "m_MaxUpgradeLevel_" + rarity);
            return val == null ? -1 : SafeInt(val);
        }

        private void ApplyModuleTypeSwap()
        {
            if (_selectedModuleIndex < 0) { Log("Select a module first (press ] to step into module 0)."); return; }
            if (_selectedCandidateIndex < 0 || _selectedCandidateIndex >= _moduleCandidates.Count)
            {
                Log("No module type browsed - press , or . to pick one first.");
                return;
            }

            var blueprints = GetBlueprintsSnapshot();
            if (_selectedBlueprintIndex >= blueprints.Count) { Log("No blueprint selected."); return; }
            object bp = blueprints[_selectedBlueprintIndex];
            object generatedData = GetInstanceMemberValue(bp, "m_GeneratedData");
            object module = GetModuleAt(generatedData, _selectedModuleIndex);
            if (module == null) { Log("Module index out of range."); return; }

            var candidate = _moduleCandidates[_selectedCandidateIndex];

            var guidProp = module.GetType().GetProperty("m_ModuleGuid", BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Instance);
            if (guidProp == null) { Log("m_ModuleGuid property not found on module."); return; }
            guidProp.SetValue(module, candidate.Guid);

            // Resize the roll array to match how many tweakable stats the new module
            // type actually has at this module's current rarity - a mismatched length
            // is the most likely way this could misbehave, so we rebuild it fresh.
            try
            {
                object rarityObj = GetInstanceMemberValue(module, "m_Rarity");
                var getTweakables = candidate.Scriptable.GetType().GetMethod("GetTweakableValuesForRarity", BindingFlags.Public | BindingFlags.Instance);
                int rollCount = 1;
                if (getTweakables != null && rarityObj != null)
                {
                    object list = getTweakables.Invoke(candidate.Scriptable, new object[] { rarityObj });
                    var countProp = list == null ? null : list.GetType().GetProperty("Count", BindingFlags.Public | BindingFlags.Instance);
                    if (countProp != null) rollCount = Math.Max(1, (int)countProp.GetValue(list));
                }

                var rollsProp = module.GetType().GetProperty("m_BaseValueRolls", BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Instance);
                if (rollsProp != null)
                {
                    var arrayType = rollsProp.PropertyType;
                    object newArray = Activator.CreateInstance(arrayType, new object[] { rollCount });
                    var itemProp = arrayType.GetProperty("Item", BindingFlags.Public | BindingFlags.Instance);
                    if (itemProp != null)
                    {
                        for (int i = 0; i < rollCount; i++)
                            itemProp.SetValue(newArray, 0.5f, new object[] { i });
                    }
                    rollsProp.SetValue(module, newArray);
                    Log($"Rebuilt roll array with {rollCount} mid-range value(s) for the new module type.");
                }
            }
            catch (Exception ex)
            {
                Log("Could not resize roll array (module GUID was still swapped): " + ex.Message);
            }

            Log($"[UNOFFICIAL] Module[{_selectedModuleIndex}] on blueprint [{_selectedBlueprintIndex}] swapped to '{candidate.DisplayName}'. Check it in the assembler UI before doing anything else.");
            SaveNow();
        }

        private void PrintBlueprintList()
        {
            var blueprints = GetBlueprintsSnapshot();
            Log($"--- {blueprints.Count} blueprints ---");
            for (int i = 0; i < blueprints.Count; i++)
            {
                object bp = blueprints[i];
                object generatedData = GetInstanceMemberValue(bp, "m_GeneratedData");
                string name = AsString(GetInstanceMemberValue(generatedData, "ResolvedName"));
                object rarity = GetInstanceMemberValue(generatedData, "m_Rarity");
                object level = GetInstanceMemberValue(generatedData, "m_Level");
                object slot = GetInstanceMemberValue(bp, "m_SlotIndex");
                int moduleCount = GetModuleCount(generatedData);
                Log($"  [{i}] {name}  Rarity={rarity} Level={level} Slot={slot} Modules={moduleCount}");
            }
            Log("Use PageUp/PageDown to select a blueprint, [ / ] to select a module within it.");
        }

        // ---------- deep diagnostics ----------

        private void HandleDebugDump(HttpListenerContext ctx)
        {
            int bpIndex = QueryInt(ctx, "blueprintIndex", _selectedBlueprintIndex);
            DumpBlueprintDeep(bpIndex);
            WriteJson(ctx, 200, "{\"ok\":true,\"note\":\"check the MelonLoader console or Editor_Log.txt for the dump\"}");
        }

        private void HandleInventoryDebugDump(HttpListenerContext ctx)
        {
            int index = QueryInt(ctx, "index", 0);
            DumpInventoryItemDeep(index);
            WriteJson(ctx, 200, "{\"ok\":true,\"note\":\"check the MelonLoader console or Editor_Log.txt for the dump\"}");
        }

        private void HandleSearchModuleDatabase(HttpListenerContext ctx)
        {
            SearchForModuleDatabase();
            WriteJson(ctx, 200, "{\"ok\":true,\"note\":\"check the MelonLoader console or Editor_Log.txt for candidates\"}");
        }

        // FindObjectsOfType<ItemModuleScriptable> reliably comes back with 0
        // results (confirmed live, while actually viewing an item's modules
        // rendered on screen) - so these scriptables clearly aren't tracked as
        // "live scene objects" the way Unity's FindObjectsOfType expects. But
        // the game itself obviously CAN resolve a module GUID to real data
        // (names, descriptions, icons all render correctly in the assembler
        // UI), which means there's some other static database/registry class
        // holding these references that we haven't found yet. This scans every
        // loaded type for static fields/properties/methods that plausibly hand
        // back ItemModuleScriptable instances (directly, or via a collection,
        // or via a string-guid lookup method) so we can find the real path in.
        // Full-parameter dump of every field/property/method (static + instance,
        // public + nonpublic) on a type, found by full name. Used to look for
        // a proper "regenerate this item" entry point - our theory (backed by
        // DiagnoseUserDataStability showing perfectly stable reads until we
        // write to m_Rarity/m_ModuleGuid, at which point the very next read
        // is a different object) is that this game re-derives an item's real
        // data from its m_Seed whenever those fields look inconsistent, and
        // the official level-up methods must call something that keeps that
        // regeneration in sync, which direct field writes never do.
        private void DumpTypeMembersByName(string typeFullName)
        {
            var t = FindType(typeFullName);
            if (t == null) { Log($"DumpTypeMembersByName: type '{typeFullName}' not found."); return; }

            var flags = BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Static | BindingFlags.Instance;
            Log($"=== Full member dump for {typeFullName} ===");

            try
            {
                foreach (var f in t.GetFields(flags))
                    Log($"  [field]  {(f.IsStatic ? "static " : "")}{f.FieldType.Name} {f.Name}");
            }
            catch (Exception ex) { Log("  GetFields threw: " + ex.Message); }

            try
            {
                foreach (var p in t.GetProperties(flags))
                    Log($"  [prop]   {p.PropertyType.Name} {p.Name}");
            }
            catch (Exception ex) { Log("  GetProperties threw: " + ex.Message); }

            try
            {
                foreach (var m in t.GetMethods(flags))
                {
                    var ps = new List<string>();
                    foreach (var pp in m.GetParameters()) ps.Add(pp.ParameterType.Name + " " + pp.Name);
                    Log($"  [method] {(m.IsStatic ? "static " : "")}{m.ReturnType.Name} {m.Name}({string.Join(", ", ps)})");
                }
            }
            catch (Exception ex) { Log("  GetMethods threw: " + ex.Message); }

            Log($"=== end dump for {typeFullName} ===");
        }

        private void DumpItemGeneratorShape()
        {
            DumpTypeMembersByName("Il2CppKeepsake.GeneratedItems.ItemGenerator");
        }

        // For "grey out Upgrade Level once a blueprint hits its cap" (same
        // idea as the module max-level display, which reads a confirmed real
        // field - m_MaxUpgradeLevel_<Rarity> - off ItemModuleScriptable). No
        // equivalent field/method for the BLUEPRINT's own overall level is
        // confirmed yet, so rather than guess a formula (which rarities cap
        // at what level is not something to assume - modules turned out to
        // all cap at 5 regardless of rarity, which is not what you'd expect
        // going in), this dumps everything that could reveal it: the full
        // member list of MetaProgressionManager (looking for a method whose
        // name suggests a max/cap - "CanUpgradeBlueprint", "GetMaxLevel",
        // etc.) and the full live shape+values of one real owned blueprint
        // (looking for a field like m_MaxLevel alongside the m_Level we
        // already read).
        private void DumpBlueprintLevelCapDiscovery()
        {
            Log("========== BLUEPRINT LEVEL CAP DISCOVERY ==========");
            if (_mgrType == null) { Log("MetaProgressionManager type not found."); }
            else DumpTypeMembersByName("Il2CppKeepsake.MetaProgression.MetaProgressionManager");

            var blueprints = GetBlueprintsSnapshot();
            if (blueprints.Count == 0)
            {
                Log("No owned blueprints right now to sample a live shape from.");
            }
            else
            {
                DumpValueShapeAndValues(blueprints[0], "sample Blueprint (owned[0])");
            }
            Log("========== END BLUEPRINT LEVEL CAP DISCOVERY ==========");
        }

        // Follow-up to Item Template Discovery: PersistentScriptableLibrary
        // exposes m_WeaponEntriesByGuid (Dictionary<string, WeaponEntry>) and
        // AllShipComponents/ShipComponentByGuid (List/Dictionary of
        // Spaceship_CompData_Base) - dumps both. Two things this could answer
        // at once: (1) whether the WeaponEntry dictionary's guid keys are real
        // GeneratedItem.m_TemplateGuid values, which would give on-foot
        // weapons a full swap-to catalog the same way AllShipComponents
        // already effectively does for ship parts; (2) whether WeaponEntry is
        // where an equipped scope/attachment actually lives - its method name
        // ("WeaponCosmetics") makes it a strong lead for the scope/attachment
        // investigation too.
        private void DumpWeaponAndShipTemplateCatalog()
        {
            Log("========== WEAPON/SHIP TEMPLATE CATALOG (m_WeaponEntriesByGuid + AllShipComponents) ==========");

            var libType = FindType("Il2CppKeepsake.GeneratedItems.Cosmetics.PersistentScriptableLibrary");
            if (libType == null) { Log("PersistentScriptableLibrary type not found."); return; }

            object weaponDict = null;
            try { weaponDict = GetStaticMemberValue(libType, "m_WeaponEntriesByGuid"); }
            catch (Exception ex) { Log("DumpWeaponAndShipTemplateCatalog: reading m_WeaponEntriesByGuid threw: " + ex.Message); }

            if (weaponDict == null)
            {
                Log("m_WeaponEntriesByGuid returned null (library may not be loaded yet).");
            }
            else
            {
                var entries = ReadIndexedCollection(weaponDict);
                Log($"---- m_WeaponEntriesByGuid: {entries.Count} entr(y/ies) - full WeaponEntry shape for up to 3 samples ----");
                int shown = 0;
                foreach (var kv in entries)
                {
                    if (shown >= 3) break;
                    object key = GetInstanceMemberValue(kv, "Key");
                    object value = GetInstanceMemberValue(kv, "Value");
                    DumpValueShapeAndValues(value, $"WeaponEntry[{key}]");
                    shown++;
                }
                var keys = new StringBuilder();
                foreach (var kv in entries)
                {
                    object key = GetInstanceMemberValue(kv, "Key");
                    if (keys.Length > 0) keys.Append(", ");
                    keys.Append(key);
                }
                Log("---- all m_WeaponEntriesByGuid keys ----");
                Log("  " + keys);
            }

            object shipList = null;
            try { shipList = GetStaticMemberValue(libType, "AllShipComponents"); }
            catch (Exception ex) { Log("DumpWeaponAndShipTemplateCatalog: reading AllShipComponents threw: " + ex.Message); }

            if (shipList == null)
            {
                Log("AllShipComponents returned null (library may not be loaded yet).");
            }
            else
            {
                var comps = ReadIndexedCollection(shipList);
                Log($"---- AllShipComponents: {comps.Count} entr(y/ies) - full shape for up to 3 samples ----");
                for (int i = 0; i < comps.Count && i < 3; i++)
                    DumpValueShapeAndValues(comps[i], $"ship component[{i}]");

                // The bit actually needed to widen "Change Base Item" to the full
                // catalog for ship components (not just weapons): every entry's
                // runtime type turned out to be the same Spaceship_CompData_Base
                // for all 31 (no per-category subclass split like hoped), but
                // m_typeOfItem (an ItemType enum) looks like the real signal -
                // confirmed "AUXPower" on real Aux Generator entries. Dumping it
                // for all 31 here to see whether it actually splits cleanly into
                // the other 7 categories too. Compact one-line-per-entry on
                // purpose so all 31 fit in the log without needing "full shape"
                // for each.
                Log($"---- ALL {comps.Count} AllShipComponents entries: guid | name | m_typeOfItem (send me this list) ----");
                for (int i = 0; i < comps.Count; i++)
                {
                    string guid = GetInstanceMemberValue(comps[i], "m_AssetGUID") as string;
                    string displayName = GetInstanceMemberValue(comps[i], "ItemDisplayName") as string;
                    string typeOfItem = GetInstanceMemberValue(comps[i], "m_typeOfItem")?.ToString();
                    Log($"  [{i}] {displayName}  guid={guid}  typeOfItem={typeOfItem}");
                }
            }

            Log("========== END WEAPON/SHIP TEMPLATE CATALOG ==========");
        }

        // First step toward "swap the item itself" (e.g. CX-305 Sideclip ->
        // some other weapon), same as the module catalog work: find where
        // the game keeps its list of item TEMPLATES (the counterpart to
        // GeneratedItem.m_TemplateGuid) and how it builds a GeneratedItem
        // from one, before writing any code that guesses at it.
        // PersistentScriptableLibrary already turned out to hold
        // AllItemModules for modules - dumping its FULL shape should reveal
        // whatever it calls the equivalent item list. GenerationConfig is
        // the other prime suspect: it's what GetModuleWeightsForItem reads
        // from for module rolls, so it may also carry per-slot/category item
        // template lists or generation rules.
        private void DumpItemTemplateDiscovery()
        {
            Log("========== ITEM TEMPLATE DISCOVERY (looking for how to swap an item's TYPE, e.g. Sideclip -> Scorpion) ==========");
            DumpTypeMembersByName("Il2CppKeepsake.GeneratedItems.Cosmetics.PersistentScriptableLibrary");

            if (_itemGeneratorType == null) _itemGeneratorType = FindType("Il2CppKeepsake.GeneratedItems.ItemGenerator");
            if (_itemGeneratorType != null)
            {
                var configProp = _itemGeneratorType.GetProperty("GenerationConfig", BindingFlags.Public | BindingFlags.Static);
                object config = null;
                try { config = configProp?.GetValue(null); }
                catch (Exception ex) { Log("DumpItemTemplateDiscovery: reading GenerationConfig threw: " + ex.Message); }

                if (config != null)
                {
                    Log("---- ItemGenerator.GenerationConfig live shape (this is what module rerolls already read for weighting - may also hold the item template list/rules) ----");
                    DumpValueShapeAndValues(config, "GenerationConfig");
                }
                else
                {
                    Log("ItemGenerator.GenerationConfig returned null, or the property wasn't found.");
                }
            }
            else
            {
                Log("ItemGenerator type not found.");
            }

            Log("Also run 'Dump ItemGenerator' from this same dropdown if you haven't already this session - looking specifically for a method that builds a full GeneratedItem from a template guid + rarity (something like GenerateItem/BuildItem/CreateGeneratedItem). If one exists, that's the safe way to do a full item swap - call the game's own logic instead of hand-splicing fields, same approach as the module reroll feature.");
            Log("========== END ITEM TEMPLATE DISCOVERY ==========");
        }

        // Investigates why some carried inventory items show a null
        // ResolvedName (confirmed via a real Deep Dump: an affected item's
        // m_GeneratedData has IsGenerated=False, m_TemplateGuid=null,
        // m_Modules=null, m_Cosmetics=null - it's not a "generated" item at
        // all, just an empty placeholder GeneratedItem). The InventoryItem's
        // OWN m_GUID is confirmed non-null though, and is presumably an asset
        // guid into some separate consumable/pickup template catalog - the
        // same way weapons/ship components resolve through
        // PersistentScriptableLibrary rather than through
        // GeneratedItem.ResolvedName. This hunts for that catalog: first
        // checks PersistentScriptableLibrary's own static members for
        // anything not already accounted for (the weapon dict/ship list/
        // cosmetics/modules collections all already confirmed), then falls
        // back to a narrower full-assembly scan (same style
        // SearchForModuleDatabase already uses successfully) for any other
        // static collection that looks like a template catalog.
        // Ground-truth check for the "Change Consumable" filter itself, added
        // after two rounds of name-based fixes (case-insensitivity, then
        // explicit ConfirmedConsumableNames/ConfirmedBlueprintNames overrides)
        // still didn't fully resolve user-reported misclassifications
        // (Expendable Minigun showing as a blueprint; Heat Blade/Wrench
        // showing as consumables). Rather than guess a fourth set of exact
        // strings, this dumps every real name IsSwappableConsumableGuid sees
        // plus its verdict and which layer decided it, so any remaining
        // mismatch (spelling, whitespace, an item missing from one catalog
        // entirely) is visible directly instead of assumed.
        private void DumpConsumableFilterDebug()
        {
            Log("========== CONSUMABLE FILTER DEBUG ==========");

            if (_craftableNamesByGuid.Count == 0) RefreshCraftableNames();
            if (_templateOriginalNames.Count == 0) RefreshTemplateOriginalNames();

            Log($"---- _templateOriginalNames: {_templateOriginalNames.Count} entr(y/ies) from m_WeaponEntriesByGuid + AllShipComponents (this is what the name-match checks against) ----");
            foreach (var kv in _templateOriginalNames)
                Log($"  guid={kv.Key}  name=\"{kv.Value}\"");

            var knownBlueprintNames = new HashSet<string>(_templateOriginalNames.Values, StringComparer.OrdinalIgnoreCase);

            Log($"---- _craftableNamesByGuid: {_craftableNamesByGuid.Count} entr(y/ies) from CraftablesLibrary.LazyUnlockToCraftable, with filter verdict + reason ----");
            foreach (var kv in _craftableNamesByGuid)
            {
                string guid = kv.Key;
                string name = kv.Value;
                _craftableCategoryByGuid.TryGetValue(guid, out var category);

                string reason;
                bool swappable;
                if (ConfirmedConsumableNames.Contains(name)) { swappable = true; reason = "ConfirmedConsumableNames override"; }
                else if (ConfirmedBlueprintNames.Contains(name)) { swappable = false; reason = "ConfirmedBlueprintNames override"; }
                else if (knownBlueprintNames.Contains(name)) { swappable = false; reason = "name-match against _templateOriginalNames"; }
                else if (_consumableCategoryWhitelist.Count == 0) { swappable = true; reason = "no category signal - default allow"; }
                else if (!_craftableCategoryByGuid.ContainsKey(guid)) { swappable = true; reason = "category unreadable - default allow"; }
                else { swappable = _consumableCategoryWhitelist.Contains(category); reason = swappable ? "category whitelist match" : "category whitelist miss"; }

                Log($"  guid={guid}  name=\"{name}\"  category={category ?? "(none)"}  swappable={swappable}  reason=[{reason}]");
            }

            Log("========== END CONSUMABLE FILTER DEBUG ==========");
        }

        // Every attempt so far (type-name scan, string-value scan, object-
        // reference scan, Harmony getter traces) searched by C# CLASS name
        // or by field VALUES - never by how the object is actually named in
        // the Unity scene hierarchy, which is frequently completely
        // different from the component's class name (a GameObject named
        // "HotbarSlot_0" might host a component literally called
        // "ItemDisplayWidget" or something equally generic that none of the
        // class-name hints would ever match). This scans every live
        // Transform's GameObject NAME instead, and for any match, lists
        // every component actually attached to it plus its full parent
        // hierarchy path - meant as a safe, cheap step BEFORE broader method
        // patching (finding the real component first makes any subsequent
        // Harmony patching surgical - patch its actual methods - instead of
        // blindly patching across the whole assembly, which risks crashing
        // or hanging the game for little benefit).
        private void DumpHotbarGameObjectDiscovery()
        {
            Log("========== HOTBAR GAMEOBJECT DISCOVERY ==========");

            string[] nameHints = { "Hotbar", "Hot Bar", "QuickSlot", "Quick Slot", "ActionBar", "Action Bar", "ItemSlot", "Item Slot", "InventorySlot", "Inventory Slot", "Consumable", "Belt", "Loadout" };

            Type transformType = FindType("UnityEngine.Transform");
            if (transformType == null) { Log("Transform type not found."); Log("========== END HOTBAR GAMEOBJECT DISCOVERY =========="); return; }

            object found = TryFindAllObjectsOfType(transformType);
            if (found == null) { Log("FindObjectsOfType(Transform) returned nothing."); Log("========== END HOTBAR GAMEOBJECT DISCOVERY =========="); return; }

            List<object> transforms;
            try { transforms = ReadIndexedCollection(found); }
            catch (Exception ex) { Log("Could not read FindObjectsOfType result: " + ex.Message); Log("========== END HOTBAR GAMEOBJECT DISCOVERY =========="); return; }

            Log($"Scanning {transforms.Count} live Transform(s)/GameObject(s) for a name matching Hotbar/QuickSlot/ActionBar/ItemSlot/InventorySlot/Consumable/Belt/Loadout...");

            int matches = 0;
            foreach (var tr in transforms)
            {
                if (tr == null) continue;
                string goName = SafeGet(() => tr.GetType().GetProperty("name")?.GetValue(tr)) as string;
                if (string.IsNullOrEmpty(goName)) continue;

                bool hit = false;
                foreach (var hint in nameHints)
                {
                    if (goName.IndexOf(hint, StringComparison.OrdinalIgnoreCase) >= 0) { hit = true; break; }
                }
                if (!hit) continue;
                matches++;

                string path = BuildTransformPath(tr);

                var componentNames = new List<string>();
                try
                {
                    object go = SafeGet(() => tr.GetType().GetProperty("gameObject")?.GetValue(tr));
                    var getComponentsMethod = go?.GetType().GetMethod("GetComponents", new[] { typeof(Type) });
                    object compType = FindType("UnityEngine.Component");
                    if (go != null && getComponentsMethod != null && compType != null)
                    {
                        object comps = SafeGet(() => getComponentsMethod.Invoke(go, new object[] { compType }));
                        if (comps != null)
                        {
                            foreach (var c in ReadIndexedCollection(comps))
                                if (c != null) componentNames.Add(c.GetType().Name);
                        }
                    }
                }
                catch { }

                Log($"  MATCH: \"{goName}\" at path \"{path}\" - components: [{string.Join(", ", componentNames)}]");
            }

            Log($"---- {matches} GameObject name match(es) found across {transforms.Count} live Transform(s). ----");
            if (matches > 0) Log("Send this log along - DumpValueShapeAndValues can be pointed at whichever component's type looks most relevant (not the Transform/RectTransform/Canvas ones) to inspect its fields and find its refresh method.");
            else Log("No name matches either. At this point the hotbar's real GameObject name doesn't contain any of the hints above - either a different name guess is needed, or the next step is broader method patching without a narrowed-down target.");
            Log("========== END HOTBAR GAMEOBJECT DISCOVERY ==========");
        }

        // Walks up transform.parent repeatedly to build a "Grandparent/Parent/
        // Child" style path string for a live Transform, for readability in
        // logs (so a match can actually be found again in the scene by hand
        // if needed, not just by name alone).
        private string BuildTransformPath(object transform)
        {
            var names = new List<string>();
            object cur = transform;
            int guard = 0;
            while (cur != null && guard++ < 50)
            {
                string n = SafeGet(() => cur.GetType().GetProperty("name")?.GetValue(cur)) as string;
                names.Insert(0, n ?? "?");
                cur = SafeGet(() => cur.GetType().GetProperty("parent")?.GetValue(cur));
            }
            return string.Join("/", names);
        }

        // Follow-up to DumpHotbarGameObjectDiscovery, which found no genuine
        // hotbar-named GameObject (its only 2 "Belt" hits were substring
        // false positives - "Ironbelt" and "LabelText"/"...abelText..."),
        // but that SAME run's raw log incidentally showed a real, live
        // GameObject named "[Dummy] Ironbelt LMG (Keepsake.RuntimeItemDummy+
        // DummyKey)". RuntimeItemDummy is a real confirmed type name, not a
        // guess - the game visibly instantiates one per held/equipped item.
        // Different strategy from trying to find+patch whatever renders the
        // hotbar: instead, find the game's OWN "give the player this item"
        // pathway (the same one that runs when you drop an item and pick it
        // back up in the hangar) and call THAT after an edit, so the game's
        // own real code does the refreshing instead of us reverse-engineering
        // it. This scans for RuntimeItemDummy's full shape + live instances,
        // plus any other Pickup/Interact/Equip/Loot/Wield/Hold-named type
        // that might expose the method to call.
        private void DumpPickupSystemDiscovery()
        {
            Log("========== PICKUP SYSTEM DISCOVERY ==========");

            string[] nameHints = { "Pickup", "PickUp", "Dummy", "Loot", "Interact", "Equip", "Wield", "Hold" };
            var candidateTypes = new List<Type>();

            foreach (var asm in AppDomain.CurrentDomain.GetAssemblies())
            {
                Type[] types;
                try { types = asm.GetTypes(); }
                catch (ReflectionTypeLoadException rtle)
                {
                    var loaded = new List<Type>();
                    foreach (var rt in rtle.Types) if (rt != null) loaded.Add(rt);
                    types = loaded.ToArray();
                }
                catch { continue; }

                foreach (var t in types)
                {
                    if (t == null) continue;
                    foreach (var hint in nameHints)
                    {
                        if (t.Name.IndexOf(hint, StringComparison.OrdinalIgnoreCase) >= 0)
                        {
                            candidateTypes.Add(t);
                            break;
                        }
                    }
                }
            }

            Log($"---- {candidateTypes.Count} type(s) with a name matching Pickup/Dummy/Loot/Interact/Equip/Wield/Hold ----");
            foreach (var t in candidateTypes) Log($"  {t.FullName}");

            if (candidateTypes.Count == 0)
            {
                Log("  No name matches anywhere in loaded assemblies - not even RuntimeItemDummy, which is odd since a live instance of it was seen in a prior scan. Send this log along.");
                Log("========== END PICKUP SYSTEM DISCOVERY ==========");
                return;
            }

            // Full member dump + live-instance shapes for the highest-value
            // candidates only (RuntimeItemDummy specifically, plus anything
            // literally named "Pickup...") - the rest are just logged by name
            // above to keep this from dumping dozens of huge member lists.
            foreach (var t in candidateTypes)
            {
                bool highValue = string.Equals(t.Name, "RuntimeItemDummy", StringComparison.OrdinalIgnoreCase)
                    || t.Name.IndexOf("Pickup", StringComparison.OrdinalIgnoreCase) >= 0
                    || t.Name.IndexOf("PickUp", StringComparison.OrdinalIgnoreCase) >= 0;
                if (!highValue) continue;

                Log($"---- Full member dump: {t.FullName} ----");
                DumpTypeMembersByName(t.FullName);

                object found = TryFindAllObjectsOfType(t);
                if (found == null) { Log($"  {t.FullName}: FindObjectsOfType returned null/nothing (no live instance right now)."); continue; }
                List<object> instances;
                try { instances = ReadIndexedCollection(found); }
                catch (Exception ex) { Log($"  {t.FullName}: could not read FindObjectsOfType result as a collection - {ex.Message}"); continue; }

                Log($"  {t.FullName}: {instances.Count} live instance(s) found in the scene.");
                for (int i = 0; i < instances.Count && i < 4; i++)
                    DumpValueShapeAndValues(instances[i], $"{t.Name}[{i}]");
            }

            Log("Send this log along - looking for a method on RuntimeItemDummy (or whichever Pickup-named type) that takes an item/guid and can be called directly after a swap to trigger the same refresh a real in-world pickup causes.");
            Log("========== END PICKUP SYSTEM DISCOVERY ==========");
        }

        // DumpPickupSystemDiscovery's full member dump of
        // Il2CppKeepsake.PlayerPickupableItemHandler turned up a very strong
        // lead: it's a per-player MonoBehaviour holding PickedUpItems (an
        // IReadOnlyReactiveCollection<PersistentPickupable> - almost
        // certainly the actual backing collection for the "hotbar", given it
        // also exposes OnSelectItem(int index)/Handle_NextItem/
        // Handle_PreviousItem/Handle_CycleItems, i.e. slot-cycling by index),
        // ItemHeld/ItemHeldPersistentPickupable (what's currently in-hand),
        // and - most importantly - a private no-arg RefreshHeldItem() method
        // plus Handle_ItemAdded(PersistentPickupable)/
        // Handle_AnyPlayerPickedUpItem(PersistentPickupable) event handlers.
        // This dumps the live instance(s) and everything in PickedUpItems so
        // it's clear whether this collection's entries actually correspond
        // to the 3 carried inventory items this tool edits.
        private void DumpPlayerPickupableItemHandlerDiscovery()
        {
            Log("========== PLAYER PICKUPABLE ITEM HANDLER DISCOVERY ==========");

            Type handlerType = FindType("Il2CppKeepsake.PlayerPickupableItemHandler");
            if (handlerType == null) { Log("PlayerPickupableItemHandler type not found."); Log("========== END PLAYER PICKUPABLE ITEM HANDLER DISCOVERY =========="); return; }

            object found = TryFindAllObjectsOfType(handlerType);
            if (found == null) { Log("FindObjectsOfType(PlayerPickupableItemHandler) returned nothing."); Log("========== END PLAYER PICKUPABLE ITEM HANDLER DISCOVERY =========="); return; }

            List<object> instances;
            try { instances = ReadIndexedCollection(found); }
            catch (Exception ex) { Log("Could not read FindObjectsOfType result: " + ex.Message); Log("========== END PLAYER PICKUPABLE ITEM HANDLER DISCOVERY =========="); return; }

            Log($"---- {instances.Count} live PlayerPickupableItemHandler instance(s) found (one per player - local player's is whichever has non-empty PickedUpItems/ItemHeld) ----");

            for (int i = 0; i < instances.Count; i++)
            {
                object inst = TryCastToType(instances[i], handlerType);
                Log($"-- instance[{i}] (GetType()={inst?.GetType().FullName}) --");
                DumpValueShapeAndValues(inst, $"PlayerPickupableItemHandler[{i}]");

                object pickedUpItems = SafeGet(() => GetInstanceMemberValue(inst, "PickedUpItems"));
                if (pickedUpItems == null) { Log($"  instance[{i}]: PickedUpItems is null."); continue; }
                List<object> entries;
                try { entries = ReadIndexedCollection(pickedUpItems); }
                catch (Exception ex) { Log($"  instance[{i}]: PickedUpItems could not be read as a collection - {ex.Message}"); continue; }

                Log($"  instance[{i}]: PickedUpItems has {entries.Count} entr(y/ies).");
                for (int e = 0; e < entries.Count; e++)
                    DumpValueShapeAndValues(entries[e], $"PlayerPickupableItemHandler[{i}].PickedUpItems[{e}]");
            }

            Log("Send this log along - if PickedUpItems' entries carry a guid matching the current inventory items, RefreshHeldItem()/Handle_ItemAdded on this handler are the next things to try calling directly.");
            Log("========== END PLAYER PICKUPABLE ITEM HANDLER DISCOVERY ==========");
        }

        // Low-risk (not a blind broad-patch sweep) action: finds every live
        // PlayerPickupableItemHandler instance and calls its private no-arg
        // RefreshHeldItem() - a method that already exists in the game's own
        // code specifically to resync the currently-held/displayed item,
        // rather than trying to simulate a full drop+pickup (which would
        // also require spawning a real world object). Logs ItemHeld's
        // resolved name before and after the call on each instance so it's
        // obvious from the log whether this actually changed anything.
        private void TryRefreshHeldItem()
        {
            Log("========== TRY REFRESH HELD ITEM ==========");

            Type handlerType = FindType("Il2CppKeepsake.PlayerPickupableItemHandler");
            if (handlerType == null) { Log("PlayerPickupableItemHandler type not found."); Log("========== END TRY REFRESH HELD ITEM =========="); return; }

            // GetMethod(name, BindingFlags) with only NonPublic|Instance came
            // back null on a real run even though RefreshHeldItem is a
            // confirmed real method (seen in DumpTypeMembersByName's own
            // dump of this exact type) - this codebase's established
            // convention (used everywhere else, e.g. DumpTypeMembersByName)
            // is to always combine all 4 flags together for interop
            // reflection to behave reliably, so GetMethods() + a manual name
            // match is used here instead of the single-name overload.
            MethodInfo refreshMethod = null;
            foreach (var m in handlerType.GetMethods(BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Static | BindingFlags.Instance))
            {
                if (m.Name == "RefreshHeldItem" && m.GetParameters().Length == 0) { refreshMethod = m; break; }
            }
            if (refreshMethod == null) { Log("RefreshHeldItem method not found via reflection."); Log("========== END TRY REFRESH HELD ITEM =========="); return; }

            object found = TryFindAllObjectsOfType(handlerType);
            if (found == null) { Log("FindObjectsOfType(PlayerPickupableItemHandler) returned nothing."); Log("========== END TRY REFRESH HELD ITEM =========="); return; }

            List<object> instances;
            try { instances = ReadIndexedCollection(found); }
            catch (Exception ex) { Log("Could not read FindObjectsOfType result: " + ex.Message); Log("========== END TRY REFRESH HELD ITEM =========="); return; }

            Log($"Found {instances.Count} live instance(s). Calling RefreshHeldItem() on each and logging ItemHeld's name before/after...");

            for (int i = 0; i < instances.Count; i++)
            {
                object inst = TryCastToType(instances[i], handlerType);
                string before = SafeGet(() => DescribeItemHeld(inst)) as string ?? "?";
                try
                {
                    refreshMethod.Invoke(inst, null);
                    string after = SafeGet(() => DescribeItemHeld(inst)) as string ?? "?";
                    Log($"  instance[{i}]: RefreshHeldItem() invoked OK. ItemHeld before='{before}' after='{after}'.");
                }
                catch (Exception ex)
                {
                    Log($"  instance[{i}]: RefreshHeldItem() threw: {ex.InnerException?.Message ?? ex.Message}");
                }
            }

            Log("========== END TRY REFRESH HELD ITEM ==========");
        }

        private string DescribeItemHeld(object handlerInstance)
        {
            object itemHeld = GetInstanceMemberValue(handlerInstance, "ItemHeld");
            if (itemHeld == null) return "(null)";
            object name = SafeGet(() => GetInstanceMemberValue(itemHeld, "ItemDisplayText")) ??
                          SafeGet(() => GetInstanceMemberValue(itemHeld, "DisplayName"));
            return (name as string) ?? itemHeld.GetType().Name;
        }

        // User confirmed: a consumable swap writes correctly (Deep Dump
        // proves it, and PushInventoryLive's before/after log proved the
        // manager's own live inventory ALSO already reflects it, before
        // SetPlayerPersistentInventory was even called - so persisted data
        // was never the problem), but the on-screen "hotbar" never shows the
        // change, even after a respawn/reload. That rules out both a
        // save-data bug and a simple stale-UI-cache theory - something else
        // must be the actual source of truth for what the hotbar renders.
        // This hunts for it directly: scans every loaded type for a name
        // that suggests a hotbar/quickslot/consumable-slot UI component,
        // then (for anything that looks like a live MonoBehaviour, not a
        // ScriptableObject asset) uses FindObjectsOfType to pull real scene
        // instances and dumps their full shape - looking for a field that
        // holds its own copy/reference to an item or guid, separate from
        // MetaProgressionManager entirely.
        private void DumpHotbarUIDiscovery()
        {
            Log("========== HOTBAR UI DISCOVERY ==========");

            string[] nameHints = { "Hotbar", "QuickSlot", "Quickslot", "ConsumableSlot", "ItemSlot", "InventorySlot", "ConsumableUI", "ConsumableHud", "ConsumableHUD" };
            var candidateTypes = new List<Type>();

            foreach (var asm in AppDomain.CurrentDomain.GetAssemblies())
            {
                Type[] types;
                try { types = asm.GetTypes(); }
                catch (ReflectionTypeLoadException rtle)
                {
                    var loaded = new List<Type>();
                    foreach (var rt in rtle.Types) if (rt != null) loaded.Add(rt);
                    types = loaded.ToArray();
                }
                catch { continue; }

                foreach (var t in types)
                {
                    if (t == null) continue;
                    foreach (var hint in nameHints)
                    {
                        if (t.Name.IndexOf(hint, StringComparison.OrdinalIgnoreCase) >= 0)
                        {
                            candidateTypes.Add(t);
                            break;
                        }
                    }
                }
            }

            Log($"---- {candidateTypes.Count} type(s) with a name matching Hotbar/QuickSlot/ConsumableSlot/ItemSlot/InventorySlot/ConsumableUI/ConsumableHud ----");
            foreach (var t in candidateTypes) Log($"  {t.FullName}");

            if (candidateTypes.Count == 0)
            {
                Log("  No name matches anywhere in loaded assemblies. The hotbar's real class name doesn't contain any of the hints above - send this log along and a different naming guess can be tried, or a broader scan (e.g. every live MonoBehaviour holding a String field) can be added instead.");
                Log("========== END HOTBAR UI DISCOVERY ==========");
                return;
            }

            int shown = 0;
            foreach (var t in candidateTypes)
            {
                object found = TryFindAllObjectsOfType(t);
                if (found == null) { Log($"  {t.FullName}: FindObjectsOfType returned null/nothing (likely not a live scene component, or none exist right now)."); continue; }
                List<object> instances;
                try { instances = ReadIndexedCollection(found); }
                catch (Exception ex) { Log($"  {t.FullName}: could not read FindObjectsOfType result as a collection - {ex.Message}"); continue; }

                Log($"  {t.FullName}: {instances.Count} live instance(s) found in the scene.");
                for (int i = 0; i < instances.Count && shown < 6; i++, shown++)
                    DumpValueShapeAndValues(instances[i], $"{t.Name}[{i}]");
            }

            Log("========== END HOTBAR UI DISCOVERY ==========");
        }

        // Follow-up to DumpHotbarUIDiscovery, which came back with ZERO type-
        // name matches - confirmed via a real run, so the hotbar's actual
        // class name doesn't contain Hotbar/QuickSlot/ConsumableSlot/ItemSlot/
        // InventorySlot/ConsumableUI/ConsumableHud at all, and guessing more
        // name variants is unlikely to land any better. Different approach:
        // search by VALUE instead of by name. Every currently-carried
        // inventory item's real m_GUID is known - scans every live
        // MonoBehaviour in the scene for any field/property whose value
        // equals one of those guids. Whatever component holds a match is
        // almost certainly the actual hotbar slot script, whatever it's
        // called - from there its update method (if any) can be found and
        // called directly after an edit, or the field pattern can reveal
        // where the true "what's in this slot" data lives besides
        // PersistentUserData/the manager's own inventory (both already
        // confirmed to update correctly - this is chasing whatever ELSE
        // exists that the hotbar actually renders from).
        private void DumpHotbarUIByValueDiscovery()
        {
            Log("========== HOTBAR UI BY-VALUE DISCOVERY ==========");

            var items = GetInventorySnapshot();
            var targetGuids = new HashSet<string>(StringComparer.OrdinalIgnoreCase);
            foreach (var it in items)
            {
                string g = GetInstanceMemberValue(it, "m_GUID") as string;
                if (!string.IsNullOrEmpty(g)) targetGuids.Add(g);
            }
            Log($"Searching for {targetGuids.Count} current inventory guid(s): {string.Join(", ", targetGuids)}");
            if (targetGuids.Count == 0)
            {
                Log("No inventory items to search for right now.");
                Log("========== END HOTBAR UI BY-VALUE DISCOVERY ==========");
                return;
            }

            Type monoType = FindType("UnityEngine.MonoBehaviour");
            if (monoType == null) { Log("MonoBehaviour type not found."); Log("========== END HOTBAR UI BY-VALUE DISCOVERY =========="); return; }

            object found = TryFindAllObjectsOfType(monoType);
            if (found == null) { Log("FindObjectsOfType(MonoBehaviour) returned nothing."); Log("========== END HOTBAR UI BY-VALUE DISCOVERY =========="); return; }

            List<object> instances;
            try { instances = ReadIndexedCollection(found); }
            catch (Exception ex) { Log("Could not read FindObjectsOfType result: " + ex.Message); Log("========== END HOTBAR UI BY-VALUE DISCOVERY =========="); return; }

            Log($"Scanning {instances.Count} live MonoBehaviour instance(s) for a field/property holding one of these guids...");

            int matches = 0;
            var flags = BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Instance;
            foreach (var inst in instances)
            {
                if (inst == null) continue;
                Type t = inst.GetType();
                string goName = "?";
                try
                {
                    var goProp = t.GetProperty("gameObject", BindingFlags.Public | BindingFlags.Instance);
                    object go = SafeGet(() => goProp?.GetValue(inst));
                    var nameProp = go?.GetType().GetProperty("name");
                    object n = SafeGet(() => nameProp?.GetValue(go));
                    if (n != null) goName = n.ToString();
                }
                catch { }

                try
                {
                    foreach (var f in t.GetFields(flags))
                    {
                        object val = SafeGet(() => f.GetValue(inst));
                        if (val is string s && targetGuids.Contains(s))
                        {
                            Log($"  MATCH (field): {t.FullName} on GameObject \"{goName}\" - {f.Name} = \"{s}\"");
                            matches++;
                        }
                    }
                    foreach (var p in t.GetProperties(flags))
                    {
                        if (p.GetIndexParameters().Length > 0) continue;
                        object val = SafeGet(() => p.GetValue(inst));
                        if (val is string s && targetGuids.Contains(s))
                        {
                            Log($"  MATCH (prop): {t.FullName} on GameObject \"{goName}\" - {p.Name} = \"{s}\"");
                            matches++;
                        }
                    }
                }
                catch { }
            }

            Log($"---- {matches} match(es) found across {instances.Count} live MonoBehaviour instance(s). ----");
            if (matches > 0) Log("Send this log along - DumpValueShapeAndValues can be pointed at the matching component's type next to find its update method.");
            Log("========== END HOTBAR UI BY-VALUE DISCOVERY ==========");
        }

        // Confirmed via a real run: the plain-string-field scan above found
        // ZERO matches across all 15,402 live MonoBehaviours - so no UI
        // component holds the raw guid as a direct string field/property.
        // Two remaining possibilities: (a) a UI slot instead holds a
        // REFERENCE to the actual InventoryItem/GeneratedItem object (its
        // guid would be one level deeper, inside that object, not on the
        // component itself - the previous scan wouldn't have seen it), or
        // (b) nothing is cached at all and the hotbar re-reads the manager's
        // live inventory on every refresh (in which case there's no
        // reference to find, and the real fix is finding whatever EVENT
        // triggers that refresh instead). This checks (a) first, since it's
        // findable the same way: only inspects fields/properties whose
        // DECLARED TYPE name contains InventoryItem or GeneratedItem (cheap
        // check across all 15k instances), then for just those candidates,
        // reads the actual value and compares its own m_GUID (or, for a
        // list/array of them, each element's m_GUID) against the current
        // inventory guids.
        private void DumpHotbarUIByReferenceDiscovery()
        {
            Log("========== HOTBAR UI BY-REFERENCE DISCOVERY ==========");

            var items = GetInventorySnapshot();
            var targetGuids = new HashSet<string>(StringComparer.OrdinalIgnoreCase);
            foreach (var it in items)
            {
                string g = GetInstanceMemberValue(it, "m_GUID") as string;
                if (!string.IsNullOrEmpty(g)) targetGuids.Add(g);
            }
            Log($"Searching for {targetGuids.Count} current inventory guid(s): {string.Join(", ", targetGuids)}");
            if (targetGuids.Count == 0)
            {
                Log("No inventory items to search for right now.");
                Log("========== END HOTBAR UI BY-REFERENCE DISCOVERY ==========");
                return;
            }

            Type monoType = FindType("UnityEngine.MonoBehaviour");
            if (monoType == null) { Log("MonoBehaviour type not found."); Log("========== END HOTBAR UI BY-REFERENCE DISCOVERY =========="); return; }

            object found = TryFindAllObjectsOfType(monoType);
            if (found == null) { Log("FindObjectsOfType(MonoBehaviour) returned nothing."); Log("========== END HOTBAR UI BY-REFERENCE DISCOVERY =========="); return; }

            List<object> instances;
            try { instances = ReadIndexedCollection(found); }
            catch (Exception ex) { Log("Could not read FindObjectsOfType result: " + ex.Message); Log("========== END HOTBAR UI BY-REFERENCE DISCOVERY =========="); return; }

            Log($"Scanning {instances.Count} live MonoBehaviour instance(s) for a field/property typed InventoryItem/GeneratedItem (or a list/array of either) whose value's own m_GUID matches...");

            int candidatesChecked = 0, matches = 0;
            var flags = BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Instance;
            bool TypeLooksRelevant(Type mt) => mt != null && (mt.Name.IndexOf("InventoryItem", StringComparison.OrdinalIgnoreCase) >= 0 || mt.Name.IndexOf("GeneratedItem", StringComparison.OrdinalIgnoreCase) >= 0);

            foreach (var inst in instances)
            {
                if (inst == null) continue;
                Type t = inst.GetType();
                string goName = "?";
                try
                {
                    var goProp = t.GetProperty("gameObject", BindingFlags.Public | BindingFlags.Instance);
                    object go = SafeGet(() => goProp?.GetValue(inst));
                    var nameProp = go?.GetType().GetProperty("name");
                    object n = SafeGet(() => nameProp?.GetValue(go));
                    if (n != null) goName = n.ToString();
                }
                catch { }

                try
                {
                    var members = new List<(string kind, string name, Type type, Func<object> getter)>();
                    foreach (var f in t.GetFields(flags)) members.Add(("field", f.Name, f.FieldType, () => f.GetValue(inst)));
                    foreach (var p in t.GetProperties(flags)) { if (p.GetIndexParameters().Length == 0) members.Add(("prop", p.Name, p.PropertyType, () => p.GetValue(inst))); }

                    foreach (var (kind, name, type, getter) in members)
                    {
                        bool directHit = TypeLooksRelevant(type);
                        Type genericArg0 = type.IsGenericType && type.GetGenericArguments().Length > 0 ? type.GetGenericArguments()[0] : null;
                        bool collectionHit = !directHit && (type.IsArray || type.IsGenericType) && TypeLooksRelevant(type.IsArray ? type.GetElementType() : genericArg0);
                        if (!directHit && !collectionHit) continue;
                        candidatesChecked++;

                        object val = SafeGet(getter);
                        if (val == null) continue;

                        if (directHit)
                        {
                            string g = SafeGet(() => GetInstanceMemberValue(val, "m_GUID") as string) as string;
                            if (g != null && targetGuids.Contains(g))
                            {
                                Log($"  MATCH: {t.FullName} on GameObject \"{goName}\" - {kind} {name} ({type.Name}) -> m_GUID = \"{g}\"");
                                matches++;
                            }
                        }
                        else
                        {
                            List<object> elements;
                            try { elements = ReadIndexedCollection(val); } catch { continue; }
                            foreach (var el in elements)
                            {
                                string g = SafeGet(() => GetInstanceMemberValue(el, "m_GUID") as string) as string;
                                if (g != null && targetGuids.Contains(g))
                                {
                                    Log($"  MATCH: {t.FullName} on GameObject \"{goName}\" - {kind} {name} ({type.Name}, element) -> m_GUID = \"{g}\"");
                                    matches++;
                                }
                            }
                        }
                    }
                }
                catch { }
            }

            Log($"---- {matches} match(es) found; {candidatesChecked} InventoryItem/GeneratedItem-typed field(s)/propert(y/ies) checked across {instances.Count} live MonoBehaviour instance(s). ----");
            if (matches > 0) Log("Send this log along - DumpValueShapeAndValues can be pointed at the matching component's type next to find its update/refresh method.");
            else Log("Still nothing - the hotbar likely doesn't cache a reference at all and re-reads live data on some trigger instead. Next step would be watching for that trigger (e.g. a Harmony patch/log hook on whatever method actually redraws it) rather than another static scan.");
            Log("========== END HOTBAR UI BY-REFERENCE DISCOVERY ==========");
        }

        // Three static scans (by type name, by string value, by object
        // reference) all came back with zero candidates - the hotbar isn't
        // caching a copy of the item anywhere in a live MonoBehaviour field.
        // That means it must re-read the item on some specific trigger
        // instead of polling every frame (if it polled every frame, our
        // already-confirmed-correct data write would show up immediately,
        // which it doesn't). This installs Harmony postfix hooks on the four
        // most likely read points - InventoryItem.m_GUID,
        // GeneratedItem.ResolvedName, and MetaProgressionManager's own
        // PersistentInventory/m_Inventory getters - so every call gets
        // logged (throttled to once per 250ms per getter, with a best-effort
        // stack trace) while you play. Do something in-game that SHOULD
        // update the hotbar (equip/use/drop an item is a real trigger the
        // game already handles correctly) and watch for a burst of log
        // lines - whatever's in that stack trace right when it happens is
        // the actual redraw path. IL2CPP stack traces from Harmony-patched
        // methods can be unreliable/garbled (the real caller may be native
        // code with no manageable frame) - if the trace itself isn't useful,
        // just the TIMING of which getter fires and when is still a real
        // signal on its own.
        private void StartHotbarRefreshTrace()
        {
            if (_hotbarTraceHarmony != null) { Log("StartHotbarRefreshTrace: already running - call Stop first if you want to restart it."); return; }
            try
            {
                _hotbarTraceHarmony = new HarmonyLib.Harmony("jumpspaceeditor.hotbartrace");
                int patched = 0;
                patched += TryPatchGetterWithTrace("Il2CppKeepsake.MetaProgression.InventoryItem", "m_GUID", nameof(InventoryItemGuidGetter_Postfix));
                patched += TryPatchGetterWithTrace("Il2CppKeepsake.GeneratedItems.GeneratedItem", "ResolvedName", nameof(GeneratedItemResolvedNameGetter_Postfix));
                patched += TryPatchGetterWithTrace("Il2CppKeepsake.MetaProgression.MetaProgressionManager", "PersistentInventory", nameof(ManagerPersistentInventoryGetter_Postfix));
                patched += TryPatchGetterWithTrace("Il2CppKeepsake.MetaProgression.MetaProgressionManager", "m_Inventory", nameof(ManagerInventoryFieldGetter_Postfix));
                Log($"StartHotbarRefreshTrace: {patched}/4 getter(s) patched. Watch the MelonLoader console (or Editor_Log.txt) while doing something in-game that should refresh the hotbar - every call is logged with a timestamp and best-effort caller info.");
            }
            catch (Exception ex)
            {
                Log("StartHotbarRefreshTrace failed: " + ex.Message);
                _hotbarTraceHarmony = null;
            }
        }

        private void StopHotbarRefreshTrace()
        {
            if (_hotbarTraceHarmony == null) { Log("StopHotbarRefreshTrace: not currently running."); return; }
            try { _hotbarTraceHarmony.UnpatchSelf(); Log("StopHotbarRefreshTrace: unpatched."); }
            catch (Exception ex) { Log("StopHotbarRefreshTrace: UnpatchSelf threw: " + ex.Message); }
            _hotbarTraceHarmony = null;
        }

        private int TryPatchGetterWithTrace(string typeFullName, string propertyName, string postfixMethodName)
        {
            Type t = FindType(typeFullName);
            if (t == null) { Log($"TryPatchGetterWithTrace: type '{typeFullName}' not found."); return 0; }
            MethodInfo getter = t.GetMethod("get_" + propertyName, BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Instance | BindingFlags.Static);
            if (getter == null) { Log($"TryPatchGetterWithTrace: get_{propertyName} not found on {typeFullName}."); return 0; }
            try
            {
                var postfixMethod = typeof(EditorMod).GetMethod(postfixMethodName, BindingFlags.Static | BindingFlags.NonPublic);
                _hotbarTraceHarmony.Patch(getter, postfix: new HarmonyLib.HarmonyMethod(postfixMethod));
                Log($"TryPatchGetterWithTrace: patched {typeFullName}.get_{propertyName}.");
                return 1;
            }
            catch (Exception ex) { Log($"TryPatchGetterWithTrace: patching {typeFullName}.get_{propertyName} threw: {ex.Message}"); return 0; }
        }

        // Shared logger for all four trace postfixes below - throttled per
        // label so a getter that turns out to be polled every frame doesn't
        // flood the log, and tagged with a best-effort stack trace (may show
        // nothing useful past the Harmony trampoline if the real caller is
        // native IL2CPP code with no managed frame - still worth a look).
        private static void LogHotbarTraceHit(string label)
        {
            var now = DateTime.UtcNow;
            if (_hotbarTraceLastLogAt.TryGetValue(label, out var last) && (now - last).TotalMilliseconds < 250) return;
            _hotbarTraceLastLogAt[label] = now;
            string trace = "(stack trace unavailable)";
            try { trace = new StackTrace(false).ToString(); } catch { }
            MelonLogger.Msg($"[HotbarTrace] {DateTime.Now:HH:mm:ss.fff} {label} called:\n{trace}");
        }

        private static void InventoryItemGuidGetter_Postfix() => LogHotbarTraceHit("InventoryItem.get_m_GUID");
        private static void GeneratedItemResolvedNameGetter_Postfix() => LogHotbarTraceHit("GeneratedItem.get_ResolvedName");
        private static void ManagerPersistentInventoryGetter_Postfix() => LogHotbarTraceHit("MetaProgressionManager.get_PersistentInventory");
        private static void ManagerInventoryFieldGetter_Postfix() => LogHotbarTraceHit("MetaProgressionManager.get_m_Inventory");

        private void DumpConsumableCatalogDiscovery()
        {
            Log("========== CONSUMABLE/PICKUP NAME CATALOG DISCOVERY ==========");

            var targets = new List<(int index, string guid)>();
            var items = GetInventorySnapshot();
            for (int i = 0; i < items.Count; i++)
            {
                object generatedData = GetInstanceMemberValue(items[i], "m_GeneratedData");
                string templateGuid = GetInstanceMemberValue(generatedData, "m_TemplateGuid") as string;
                if (string.IsNullOrEmpty(templateGuid))
                {
                    string invGuid = GetInstanceMemberValue(items[i], "m_GUID") as string;
                    if (!string.IsNullOrEmpty(invGuid))
                    {
                        targets.Add((i, invGuid));
                        Log($"  inventory[{i}]: m_TemplateGuid is empty (not a generated item) - hunting for its own m_GUID = {invGuid}");
                    }
                }
            }

            if (targets.Count == 0)
            {
                Log("  No inventory items with an empty m_TemplateGuid right now - nothing to hunt for (every carried item currently resolves as a normal generated item).");
                Log("========== END CONSUMABLE/PICKUP NAME CATALOG DISCOVERY ==========");
                return;
            }

            Log("---- PersistentScriptableLibrary member shape (looking for anything besides the 4 already-confirmed collections: m_WeaponEntriesByGuid, AllShipComponents, AllCosmetics, AllItemModules) ----");
            DumpTypeMembersByName("Il2CppKeepsake.GeneratedItems.Cosmetics.PersistentScriptableLibrary");

            bool foundAny = false;
            var libType = FindType("Il2CppKeepsake.GeneratedItems.Cosmetics.PersistentScriptableLibrary");
            if (libType != null)
            {
                var knownNames = new HashSet<string> { "m_WeaponEntriesByGuid", "AllShipComponents", "AllCosmetics", "AllItemModules", "ShipComponentByGuid" };
                var flags = BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Static;
                var candidateNames = new List<string>();
                try { foreach (var f in libType.GetFields(flags)) if (!knownNames.Contains(f.Name) && IsPlausibleCatalogCollection(f.FieldType)) candidateNames.Add(f.Name); } catch { }
                try { foreach (var p in libType.GetProperties(flags)) if (!knownNames.Contains(p.Name) && IsPlausibleCatalogCollection(p.PropertyType)) candidateNames.Add(p.Name); } catch { }

                Log($"---- Checking {candidateNames.Count} other static collection member(s) on PersistentScriptableLibrary for a matching guid ----");
                foreach (var name in candidateNames)
                {
                    object value = SafeGet(() => GetStaticMemberValue(libType, name));
                    if (value == null) continue;
                    if (SearchCollectionForGuids(value, $"PersistentScriptableLibrary.{name}", targets)) foundAny = true;
                }
            }
            else
            {
                Log("PersistentScriptableLibrary type not found.");
            }

            if (!foundAny)
            {
                Log("---- Nothing found on PersistentScriptableLibrary - falling back to a full-assembly scan for other static collections that look like template catalogs (declaring type name contains Library/Database/Catalog/Registry, or element type name contains Consumable/Pickup) ----");
                if (FullAssemblyCatalogGuidSearch(targets)) foundAny = true;
            }

            if (!foundAny)
            {
                Log("  No match found anywhere searched. These may be resolved through a runtime instance (not a static catalog) rather than a ScriptableObject library - e.g. a per-save inventory/item database, or a MonoBehaviour/manager instance. Send this log along and the next place to look can be narrowed down from what's here.");
            }

            Log("========== END CONSUMABLE/PICKUP NAME CATALOG DISCOVERY ==========");
        }

        private bool IsPlausibleCatalogCollection(Type t)
        {
            if (t == null) return false;
            if (t.IsArray) return true;
            if (!t.IsGenericType) return false;
            string name = t.Name;
            return name.StartsWith("List") || name.StartsWith("Dictionary") || name.StartsWith("Il2CppReferenceArray");
        }

        // Iterates a collection (list, dictionary, or Il2Cpp array) and checks
        // each entry for a guid-like member (m_GUID, m_AssetGUID, GUID,
        // AssetGUID, Guid, m_Guid, or a dictionary's own Key) matching one of
        // the target guids. Dumps the full shape+values of any match found.
        // Returns true if at least one match was found.
        private bool SearchCollectionForGuids(object collection, string label, List<(int index, string guid)> targets)
        {
            List<object> entries;
            try { entries = ReadIndexedCollection(collection); }
            catch (Exception ex) { Log($"  {label}: could not read as a collection - {ex.Message}"); return false; }

            if (entries.Count == 0) return false;
            Log($"  {label}: {entries.Count} entr(y/ies) - scanning for a guid match...");

            bool found = false;
            string[] guidMemberNames = { "m_GUID", "m_AssetGUID", "GUID", "AssetGUID", "Guid", "m_Guid" };

            foreach (var entry in entries)
            {
                // Dictionary entries come back KeyValuePair-shaped (Key/Value members).
                object keyVal = SafeGet(() => GetInstanceMemberValue(entry, "Key"));
                if (keyVal is string keyStr)
                {
                    object valVal = SafeGet(() => GetInstanceMemberValue(entry, "Value"));
                    foreach (var (index, guid) in targets)
                    {
                        if (keyStr == guid)
                        {
                            Log($"  MATCH: {label} key \"{keyStr}\" == inventory[{index}]'s m_GUID");
                            DumpValueShapeAndValues(valVal, $"{label}[\"{keyStr}\"] (Value)");
                            found = true;
                        }
                    }
                    continue;
                }

                foreach (var memberName in guidMemberNames)
                {
                    object guidValue = SafeGet(() => GetInstanceMemberValue(entry, memberName));
                    if (guidValue is string gs && !string.IsNullOrEmpty(gs))
                    {
                        foreach (var (index, guid) in targets)
                        {
                            if (gs == guid)
                            {
                                Log($"  MATCH: {label} entry.{memberName} == inventory[{index}]'s m_GUID");
                                DumpValueShapeAndValues(entry, $"{label} entry (matched via {memberName})");
                                found = true;
                            }
                        }
                        break; // found a guid-like member on this entry, no need to check the rest
                    }
                }
            }
            return found;
        }

        // Narrower cousin of SearchForModuleDatabase - only looks at static
        // collections on types whose OWN name suggests a template catalog
        // (Library/Database/Catalog/Registry), or whose element type name
        // suggests a consumable/pickup, rather than every static collection
        // in every loaded assembly (which would be both slow and mostly
        // noise for this particular hunt).
        private bool FullAssemblyCatalogGuidSearch(List<(int index, string guid)> targets)
        {
            bool foundAny = false;
            var flags = BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Static;
            int scanned = 0;

            foreach (var asm in AppDomain.CurrentDomain.GetAssemblies())
            {
                Type[] types;
                try { types = asm.GetTypes(); }
                catch (ReflectionTypeLoadException rtle)
                {
                    var loaded = new List<Type>();
                    foreach (var rt in rtle.Types) if (rt != null) loaded.Add(rt);
                    types = loaded.ToArray();
                }
                catch { continue; }

                foreach (var t in types)
                {
                    if (t == null) continue;
                    bool typeNameLooksLikeCatalog = t.Name.IndexOf("Library", StringComparison.OrdinalIgnoreCase) >= 0
                        || t.Name.IndexOf("Database", StringComparison.OrdinalIgnoreCase) >= 0
                        || t.Name.IndexOf("Catalog", StringComparison.OrdinalIgnoreCase) >= 0
                        || t.Name.IndexOf("Registry", StringComparison.OrdinalIgnoreCase) >= 0;
                    if (!typeNameLooksLikeCatalog) continue;

                    try
                    {
                        foreach (var f in t.GetFields(flags))
                        {
                            if (!IsPlausibleCatalogCollection(f.FieldType)) continue;
                            if (scanned++ > 100) { Log("  ...stopping early, 100+ candidate collections already checked."); return foundAny; }
                            object value = SafeGet(() => f.GetValue(null));
                            if (value != null && SearchCollectionForGuids(value, $"{t.FullName}.{f.Name}", targets)) foundAny = true;
                        }
                        foreach (var p in t.GetProperties(flags))
                        {
                            if (p.GetIndexParameters().Length > 0 || !IsPlausibleCatalogCollection(p.PropertyType)) continue;
                            if (scanned++ > 100) { Log("  ...stopping early, 100+ candidate collections already checked."); return foundAny; }
                            object value = SafeGet(() => p.GetValue(null));
                            if (value != null && SearchCollectionForGuids(value, $"{t.FullName}.{p.Name}", targets)) foundAny = true;
                        }
                    }
                    catch { }
                }
            }

            Log($"  Full-assembly catalog scan checked {scanned} candidate collection(s) across types named *Library*/*Database*/*Catalog*/*Registry*.");
            return foundAny;
        }

        // Checks whether an on-foot gun's scope (or other attachment) is
        // even a swappable, separate-from-modules thing at all, before
        // writing any code that assumes it is. Two-pronged, same approach as
        // finding the module catalog originally:
        //   1) scan every owned Weapons-category item's live generatedData
        //      for any field/property whose NAME suggests scope/sight/
        //      attachment/etc, and dump one level deeper into it if it's a
        //      complex (non-primitive) member - a real hit here would be a
        //      guid or a nested scriptable-shaped object.
        //   2) search every loaded type for Scope/Attachment/Sight/Optic in
        //      its name, in case there's a dedicated catalog type/library
        //      (the ItemModuleScriptable/PersistentScriptableLibrary
        //      equivalent for attachments), independent of whether step 1
        //      found anything on the item itself.
        private void DumpScopeAttachmentDiscovery()
        {
            Log("========== SCOPE/ATTACHMENT DISCOVERY (checking if on-foot gun scopes/attachments can be swapped) ==========");

            var keywords = new[] { "scope", "sight", "attach", "optic", "barrel", "muzzle", "grip", "stock", "magazine", "silencer", "suppressor" };
            var blueprints = GetBlueprintsSnapshot();
            var categoryMap = GetCategoryMap();
            var memberFlags = BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Instance;
            int checkedCount = 0, hitCount = 0;

            foreach (var bp in blueprints)
            {
                object generatedData = GetInstanceMemberValue(bp, "m_GeneratedData");
                if (generatedData == null) continue;
                string name = AsString(GetInstanceMemberValue(generatedData, "ResolvedName"));
                string categoryGuid = GetInstanceMemberValue(bp, "m_CategoryGuid") as string;
                string categoryLabel = "Unknown";
                if (name != null && KnownItemCategory.TryGetValue(name, out var known)) categoryLabel = known;
                else if (categoryGuid != null && categoryMap.TryGetValue(categoryGuid, out var info)) categoryLabel = info.name;

                // "Weapons" is the on-foot gun category (confirmed via the
                // module-kinds dump: Ironbelt LMG, SR.99 Javelin, Bulldog-SA7,
                // CX-305 Sideclip all land here) - ship weapons are their own
                // categories (Pilot Cannons, Multiturrets, Special Weapons).
                if (!string.Equals(categoryLabel, "Weapons", StringComparison.OrdinalIgnoreCase)) continue;
                checkedCount++;

                var t = generatedData.GetType();
                var hits = new List<(string kind, string memberName, Type memberType, object value)>();
                try
                {
                    foreach (var f in t.GetFields(memberFlags))
                        foreach (var kw in keywords)
                            if (f.Name.ToLowerInvariant().Contains(kw)) { hits.Add(("field", f.Name, f.FieldType, SafeGet(() => f.GetValue(generatedData)))); break; }
                }
                catch (Exception ex) { Log($"  {name}: GetFields threw: {ex.Message}"); }
                try
                {
                    foreach (var p in t.GetProperties(memberFlags))
                    {
                        if (p.GetIndexParameters().Length > 0) continue;
                        foreach (var kw in keywords)
                            if (p.Name.ToLowerInvariant().Contains(kw)) { hits.Add(("prop", p.Name, p.PropertyType, SafeGet(() => p.GetValue(generatedData)))); break; }
                    }
                }
                catch (Exception ex) { Log($"  {name}: GetProperties threw: {ex.Message}"); }

                if (hits.Count == 0) continue;
                hitCount++;
                Log($"  {name} (category={categoryLabel}): {hits.Count} keyword-matching member(s):");
                foreach (var h in hits)
                {
                    Log($"    [{h.kind}] {h.memberType.Name} {h.memberName} = {DescribeValue(h.value)}");
                    if (h.value != null && !h.memberType.IsPrimitive && h.memberType != typeof(string) && !h.memberType.IsEnum)
                        DumpValueShapeAndValues(h.value, $"      {name}.{h.memberName}");
                }
            }
            Log($"---- checked {checkedCount} Weapons-category item(s), {hitCount} had a scope/sight/attachment-ish member (keywords: {string.Join(", ", keywords)}) ----");

            Log("---- searching all loaded types for Scope/Attachment/Sight/Optic in the type name ----");
            int typeHits = 0;
            bool stop = false;
            foreach (var asm in AppDomain.CurrentDomain.GetAssemblies())
            {
                if (stop) break;
                Type[] types;
                try { types = asm.GetTypes(); }
                catch (ReflectionTypeLoadException rtle)
                {
                    var loaded = new List<Type>();
                    foreach (var rt in rtle.Types) if (rt != null) loaded.Add(rt);
                    types = loaded.ToArray();
                }
                catch { continue; }

                foreach (var t2 in types)
                {
                    if (t2?.FullName == null) continue;
                    string lower = t2.FullName.ToLowerInvariant();
                    if (!(lower.Contains("scope") || lower.Contains("attachment") || lower.Contains("sight") || lower.Contains("optic"))) continue;
                    Log($"  type match: {t2.FullName}");
                    typeHits++;
                    if (typeHits > 100) { Log("  ...stopping early, 100+ type hits - narrow this down manually from what's logged so far."); stop = true; break; }
                }
            }
            Log($"---- {typeHits} matching type(s) found ----");

            Log("========== END SCOPE/ATTACHMENT DISCOVERY ==========");
        }

        // Follow-up to DumpScopeAttachmentDiscovery: that first pass found 0
        // scope-ish fields directly on any owned Weapons-category item, but
        // the type-name search turned up
        // "Il2CppKeepsake.GeneratedItems.Cosmetics.Cosmetic_SecondaryScope"
        // plus a "CosmeticsHandler.SpawnAttachmentAsync" method - meaning
        // scopes/attachments most likely live in the game's separate
        // COSMETICS system, not as a field on GeneratedItem the way modules
        // are. This digs into that system specifically: the
        // Cosmetic_SecondaryScope type's own shape, the rest of the
        // "Cosmetic_" type family (there's probably a Cosmetic_PrimaryScope,
        // Cosmetic_Barrel, etc.), the actual cosmetics catalog
        // (PersistentScriptableLibrary.AllCosmetics - same shape of source
        // that AllItemModules turned out to be), and a check of the
        // blueprint object ITSELF (not generatedData) in case the equipped
        // cosmetic is tracked there instead of on the item.
        private void DumpCosmeticsScopeDiscovery()
        {
            Log("========== COSMETICS/SCOPE DISCOVERY (follow-up: 'Cosmetic_SecondaryScope' type found last time) ==========");

            DumpTypeMembersByName("Il2CppKeepsake.GeneratedItems.Cosmetics.Cosmetic_SecondaryScope");
            DumpTypeMembersByName("Il2CppKeepsake.GeneratedItems.Cosmetics.CosmeticsHandler");

            Log("---- searching all loaded types for a '.Cosmetic_' name segment (rest of the cosmetic-slot family, e.g. a primary scope/barrel/skin counterpart) ----");
            int familyHits = 0;
            foreach (var asm in AppDomain.CurrentDomain.GetAssemblies())
            {
                Type[] types;
                try { types = asm.GetTypes(); }
                catch (ReflectionTypeLoadException rtle)
                {
                    var loaded = new List<Type>();
                    foreach (var rt in rtle.Types) if (rt != null) loaded.Add(rt);
                    types = loaded.ToArray();
                }
                catch { continue; }
                foreach (var t in types)
                {
                    if (t?.FullName == null || !t.FullName.Contains(".Cosmetic_")) continue;
                    Log($"  cosmetic-family type: {t.FullName}");
                    familyHits++;
                }
            }
            Log($"---- {familyHits} '.Cosmetic_' type(s) found ----");

            var libType = FindType("Il2CppKeepsake.GeneratedItems.Cosmetics.PersistentScriptableLibrary");
            if (libType != null)
            {
                object allCosmetics = null;
                try { allCosmetics = GetStaticMemberValue(libType, "AllCosmetics"); }
                catch (Exception ex) { Log("DumpCosmeticsScopeDiscovery: reading AllCosmetics threw: " + ex.Message); }

                if (allCosmetics != null)
                {
                    var items = ReadIndexedCollection(allCosmetics);
                    Log($"---- PersistentScriptableLibrary.AllCosmetics: {items.Count} item(s) - dumping up to 5 sample shapes ----");
                    for (int i = 0; i < Math.Min(items.Count, 5); i++)
                        DumpValueShapeAndValues(items[i], $"AllCosmetics[{i}]");
                    if (items.Count > 5) Log($"  ... and {items.Count - 5} more");
                }
                else
                {
                    Log("PersistentScriptableLibrary.AllCosmetics returned null (library may not be loaded yet, or the property doesn't exist).");
                }
            }
            else
            {
                Log("PersistentScriptableLibrary type not found.");
            }

            Log("---- checking blueprint objects themselves (not m_GeneratedData) for cosmetic/scope/attach-named members, in case the equipped cosmetic is tracked per-blueprint rather than on the item ----");
            var bpKeywords = new[] { "cosmetic", "scope", "attach", "sight", "optic" };
            var blueprints = GetBlueprintsSnapshot();
            var categoryMap = GetCategoryMap();
            var memberFlags = BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Instance;
            int bpHits = 0;

            foreach (var bp in blueprints)
            {
                object generatedData = GetInstanceMemberValue(bp, "m_GeneratedData");
                string name = AsString(GetInstanceMemberValue(generatedData, "ResolvedName"));
                string categoryGuid = GetInstanceMemberValue(bp, "m_CategoryGuid") as string;
                string categoryLabel = "Unknown";
                if (name != null && KnownItemCategory.TryGetValue(name, out var known)) categoryLabel = known;
                else if (categoryGuid != null && categoryMap.TryGetValue(categoryGuid, out var info)) categoryLabel = info.name;
                if (!string.Equals(categoryLabel, "Weapons", StringComparison.OrdinalIgnoreCase)) continue;

                var t = bp.GetType();
                var hits = new List<(string kind, string memberName, Type memberType, object value)>();
                try
                {
                    foreach (var f in t.GetFields(memberFlags))
                        foreach (var kw in bpKeywords)
                            if (f.Name.ToLowerInvariant().Contains(kw)) { hits.Add(("field", f.Name, f.FieldType, SafeGet(() => f.GetValue(bp)))); break; }
                }
                catch (Exception ex) { Log($"  {name}: GetFields threw: {ex.Message}"); }
                try
                {
                    foreach (var p in t.GetProperties(memberFlags))
                    {
                        if (p.GetIndexParameters().Length > 0) continue;
                        foreach (var kw in bpKeywords)
                            if (p.Name.ToLowerInvariant().Contains(kw)) { hits.Add(("prop", p.Name, p.PropertyType, SafeGet(() => p.GetValue(bp)))); break; }
                    }
                }
                catch (Exception ex) { Log($"  {name}: GetProperties threw: {ex.Message}"); }

                if (hits.Count == 0) continue;
                bpHits++;
                Log($"  {name}: {hits.Count} keyword-matching member(s) on the BLUEPRINT object itself:");
                foreach (var h in hits)
                {
                    Log($"    [{h.kind}] {h.memberType.Name} {h.memberName} = {DescribeValue(h.value)}");
                    if (h.value != null && !h.memberType.IsPrimitive && h.memberType != typeof(string) && !h.memberType.IsEnum)
                        DumpValueShapeAndValues(h.value, $"      {name}.{h.memberName}");
                }
            }
            Log($"---- {bpHits} blueprint(s) had a cosmetic/scope/attach-ish member on the blueprint object itself ----");

            Log("========== END COSMETICS/SCOPE DISCOVERY ==========");
        }

        // Round 3, following up on what the last diagnostic found:
        // - Cosmetic_SecondaryScope / CosmeticsHandler are runtime scene
        //   components (MonoBehaviours - transform/gameObject/coroutines,
        //   no data fields), not save data - not useful to write to
        //   directly.
        // - CosmeticsHandler.ApplyCosmeticAsync(slotIndex, AssetReferenceT
        //   cosmeticRef, ...) and ApplyCosmeticsAsync(..., CosmeticSelection[]
        //   ...) are the real APIs - "CosmeticSelection" is presumably the
        //   per-slot record (slot + chosen cosmetic guid).
        // - PersistentScriptableLibrary.AllCosmetics is a 26-entry catalog of
        //   CosmeticData, which has m_SlotType (enum, saw "Color" already),
        //   m_CompatibleWeaponTags, m_MinRarity/m_MaxRarity, and critically
        //   an IsAttachment flag - only the first 5 (all color swaps) got
        //   dumped last time, so the actual scope/attachment entries are
        //   still unseen.
        // - Neither the item's generatedData nor the blueprint object had
        //   any member whose NAME matched our keyword list, including
        //   "cosmetic" itself (that keyword was only checked against the
        //   blueprint, not generatedData, last time) - this round also
        //   matches by the member's TYPE name instead of its member name,
        //   which is a lot more likely to actually find where an equipped
        //   cosmetic/scope selection is persisted, since we clearly guessed
        //   wrong on naming so far.
        private void DumpCosmeticSelectionDiscovery()
        {
            Log("========== COSMETIC SELECTION DISCOVERY (round 4: CosmeticSelection is in Il2CppKeepsake.GeneratedItems, NOT ...GeneratedItems.Cosmetics - round 3's DumpTypeMembersByName call had the wrong namespace, which is why it came back 'not found') ==========");

            var libType = FindType("Il2CppKeepsake.GeneratedItems.Cosmetics.PersistentScriptableLibrary");
            var allCosmetics = new List<object>();
            if (libType != null)
            {
                object raw = null;
                try { raw = GetStaticMemberValue(libType, "AllCosmetics"); }
                catch (Exception ex) { Log("DumpCosmeticSelectionDiscovery: reading AllCosmetics threw: " + ex.Message); }
                if (raw != null) allCosmetics = ReadIndexedCollection(raw);
            }

            Log($"---- AllCosmetics catalog: {allCosmetics.Count} total entries - one-line summary of every entry ----");
            int attachmentCount = 0;
            var attachments = new List<object>();
            foreach (var c in allCosmetics)
            {
                string cName = GetInstanceMemberValue(c, "name") as string;
                object slotType = GetInstanceMemberValue(c, "m_SlotType");
                object isAttachmentVal = SafeGet(() => c.GetType().GetProperty("IsAttachment", BindingFlags.Public | BindingFlags.Instance)?.GetValue(c));
                bool isAttachment = isAttachmentVal is bool b && b;
                string guid = GetInstanceMemberValue(c, "m_AssetGuid") as string;
                Log($"  {cName}  slotType={slotType}  isAttachment={isAttachment}  guid={guid}");
                if (isAttachment) { attachmentCount++; attachments.Add(c); }
            }
            Log($"---- {attachmentCount} entr(y/ies) with IsAttachment=True (guid is what you'd write into a CosmeticSelection to change the scope) ----");

            // Correct namespace this time (round 3 looked in
            // ...GeneratedItems.Cosmetics.CosmeticSelection and got "not
            // found" - the type-based member scan below found the REAL
            // fully-qualified name off GeneratedItem.m_Cosmetics itself:
            // Il2CppKeepsake.GeneratedItems.CosmeticSelection, one level up).
            DumpTypeMembersByName("Il2CppKeepsake.GeneratedItems.CosmeticSelection");

            // WeaponEntry.m_Data (PickupableItem_Data_GenericWeapon) shape -
            // checking whether its own AssetGUID matches the dictionary key
            // it's stored under in m_WeaponEntriesByGuid, which would confirm
            // those keys ARE real GeneratedItem.m_TemplateGuid values (and so
            // could widen "Change Base Item" beyond just owned templates).
            if (libType != null)
            {
                object weaponDict = null;
                try { weaponDict = GetStaticMemberValue(libType, "m_WeaponEntriesByGuid"); }
                catch (Exception ex) { Log("DumpCosmeticSelectionDiscovery: reading m_WeaponEntriesByGuid threw: " + ex.Message); }
                if (weaponDict != null)
                {
                    var entries = ReadIndexedCollection(weaponDict);
                    if (entries.Count > 0)
                    {
                        object key = GetInstanceMemberValue(entries[0], "Key");
                        object value = GetInstanceMemberValue(entries[0], "Value");
                        object data = GetInstanceMemberValue(value, "m_Data");
                        Log($"---- WeaponEntry[{key}].m_Data shape (checking if its own guid matches the dictionary key) ----");
                        DumpValueShapeAndValues(data, $"WeaponEntry[{key}].m_Data");
                    }
                }
            }

            // Live values: every owned Weapons item's actual m_Cosmetics
            // array (GeneratedItem.m_Cosmetics : CosmeticSelection[] -
            // confirmed present via the type-based scan below, but that scan
            // only prints the member's declared TYPE, not what's actually
            // inside it slot-by-slot right now).
            Log("---- live m_Cosmetics values for every owned Weapons-category item ----");
            var blueprints = GetBlueprintsSnapshot();
            var categoryMap = GetCategoryMap();
            var memberFlags = BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Instance;
            int typeHitCount = 0;

            foreach (var bp in blueprints)
            {
                object generatedData = GetInstanceMemberValue(bp, "m_GeneratedData");
                string name = AsString(GetInstanceMemberValue(generatedData, "ResolvedName"));
                string categoryGuid = GetInstanceMemberValue(bp, "m_CategoryGuid") as string;
                string categoryLabel = "Unknown";
                if (name != null && KnownItemCategory.TryGetValue(name, out var known)) categoryLabel = known;
                else if (categoryGuid != null && categoryMap.TryGetValue(categoryGuid, out var info)) categoryLabel = info.name;
                if (!string.Equals(categoryLabel, "Weapons", StringComparison.OrdinalIgnoreCase)) continue;

                object cosmetics = GetInstanceMemberValue(generatedData, "m_Cosmetics");
                if (cosmetics == null) { Log($"  {name}: m_Cosmetics is null."); continue; }
                var selections = ReadIndexedCollection(cosmetics);
                Log($"  {name}: m_Cosmetics has {selections.Count} entr(y/ies).");
                for (int i = 0; i < selections.Count; i++)
                    DumpValueShapeAndValues(selections[i], $"{name}.m_Cosmetics[{i}]");

                // Broader TYPE-based scan (not member-name-based) on both
                // generatedData and the blueprint object itself - kept from
                // round 3 as a cross-check that m_Cosmetics is really the
                // only cosmetic-typed member on these items.
                foreach (var (obj, objLabel) in new[] { (bp, "blueprint"), (generatedData, "generatedData") })
                {
                    if (obj == null) continue;
                    var t = obj.GetType();
                    try
                    {
                        foreach (var f in t.GetFields(memberFlags))
                        {
                            string fullName = f.FieldType.FullName;
                            if (fullName == null || !fullName.ToLowerInvariant().Contains("cosmetic")) continue;
                            typeHitCount++;
                            object val = SafeGet(() => f.GetValue(obj));
                            Log($"  {name}.{objLabel}.[field] {fullName} {f.Name} = {DescribeValue(val)}");
                        }
                    }
                    catch (Exception ex) { Log($"  {name}.{objLabel}: GetFields threw: {ex.Message}"); }
                    try
                    {
                        foreach (var p in t.GetProperties(memberFlags))
                        {
                            if (p.GetIndexParameters().Length > 0) continue;
                            string fullName = p.PropertyType.FullName;
                            if (fullName == null || !fullName.ToLowerInvariant().Contains("cosmetic")) continue;
                            typeHitCount++;
                            object val = SafeGet(() => p.GetValue(obj));
                            Log($"  {name}.{objLabel}.[prop] {fullName} {p.Name} = {DescribeValue(val)}");
                        }
                    }
                    catch (Exception ex) { Log($"  {name}.{objLabel}: GetProperties threw: {ex.Message}"); }
                }
            }
            Log($"---- {typeHitCount} type-based cosmetic-related member(s) found across owned Weapons items ----");

            Log("========== END COSMETIC SELECTION DISCOVERY ==========");
        }

        private void SearchForModuleDatabase()
        {
            if (_itemModuleScriptableType == null)
                _itemModuleScriptableType = FindType("Il2CppKeepsake.HyperSpace.System.Modifiers.ItemModule.ItemModuleScriptable");
            if (_itemModuleScriptableType == null) { Log("SearchForModuleDatabase: ItemModuleScriptable type not found."); return; }

            Log("=== Searching all loaded types for a module database/registry ===");
            int hits = 0;
            var flags = BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Static;

            foreach (var asm in AppDomain.CurrentDomain.GetAssemblies())
            {
                Type[] types;
                try { types = asm.GetTypes(); }
                catch (ReflectionTypeLoadException rtle)
                {
                    var loaded = new List<Type>();
                    foreach (var rt in rtle.Types) if (rt != null) loaded.Add(rt);
                    types = loaded.ToArray();
                }
                catch { continue; }

                foreach (var t in types)
                {
                    if (t == null) continue;
                    if (hits > 200) { Log("  ...stopping early, 200+ hits already - narrow this down manually from what's logged so far."); LogModuleDatabaseSearchEnd(hits); return; }

                    try
                    {
                        foreach (var f in t.GetFields(flags))
                            if (IsPlausibleModuleContainer(f.FieldType))
                            { Log($"  [static field]  {t.FullName}.{f.Name} : {f.FieldType.FullName}"); hits++; }
                    }
                    catch { }

                    try
                    {
                        foreach (var p in t.GetProperties(flags))
                            if (IsPlausibleModuleContainer(p.PropertyType))
                            { Log($"  [static prop]   {t.FullName}.{p.Name} : {p.PropertyType.FullName}"); hits++; }
                    }
                    catch { }

                    try
                    {
                        foreach (var m in t.GetMethods(flags))
                        {
                            var ps = m.GetParameters();
                            bool looksLikeGuidLookup = ps.Length == 1 && ps[0].ParameterType == typeof(string)
                                && _itemModuleScriptableType.IsAssignableFrom(m.ReturnType);
                            bool looksLikeAllGetter = ps.Length == 0 && IsPlausibleModuleContainer(m.ReturnType);
                            if (looksLikeGuidLookup || looksLikeAllGetter)
                            {
                                var paramNames = new List<string>();
                                foreach (var pp in ps) paramNames.Add(pp.ParameterType.Name);
                                Log($"  [static method] {t.FullName}.{m.Name}({string.Join(",", paramNames)}) : {m.ReturnType.FullName}");
                                hits++;
                            }
                        }
                    }
                    catch { }
                }
            }

            LogModuleDatabaseSearchEnd(hits);
        }

        private void LogModuleDatabaseSearchEnd(int hits)
        {
            Log($"=== Search complete - {hits} candidate member(s) logged above ===");
        }

        private bool IsPlausibleModuleContainer(Type t)
        {
            if (t == null || _itemModuleScriptableType == null) return false;
            if (_itemModuleScriptableType.IsAssignableFrom(t)) return true;
            if (t.IsArray && t.GetElementType() != null && _itemModuleScriptableType.IsAssignableFrom(t.GetElementType())) return true;
            if (t.IsGenericType)
            {
                foreach (var arg in t.GetGenericArguments())
                    if (_itemModuleScriptableType.IsAssignableFrom(arg)) return true;
            }
            return false;
        }

        // Full-depth dump of one blueprint: its own shape+values, its
        // generatedData, and EVERY module slot's shape+values, plus (if it
        // resolves) the matching module-type catalog entry's shape+values too.
        // This goes well beyond DumpTypeShape (which only prints member NAMES
        // when a collection read fails) - it also prints live field/property
        // VALUES wherever they're simple enough to show directly, so you can
        // see actual live game state, not just the schema.
        private void DumpBlueprintDeep(int bpIndex)
        {
            var blueprints = GetBlueprintsSnapshot();
            if (bpIndex < 0 || bpIndex >= blueprints.Count)
            {
                Log($"DumpBlueprintDeep: bad blueprint index {bpIndex} (have {blueprints.Count} blueprints - press F7 or PageUp/PageDown first).");
                return;
            }

            Log($"========== DEEP DUMP: blueprint[{bpIndex}] ==========");
            object bp = blueprints[bpIndex];
            DumpValueShapeAndValues(bp, "blueprint");

            object generatedData = GetInstanceMemberValue(bp, "m_GeneratedData");
            DumpValueShapeAndValues(generatedData, "blueprint.m_GeneratedData");

            int moduleCount = GetModuleCount(generatedData);
            Log($"  module count (m_Modules.Length): {moduleCount}");

            if (_moduleCandidates.Count == 0) RefreshModuleCandidates(false);

            for (int m = 0; m < moduleCount; m++)
            {
                object module = GetModuleAt(generatedData, m);
                Log($"---------- module[{m}] ----------");
                DumpValueShapeAndValues(module, $"module[{m}]");

                string mGuid = GetInstanceMemberValue(module, "m_ModuleGuid") as string;
                ModuleCandidate candidate = null;
                foreach (var c in _moduleCandidates) { if (c.Guid == mGuid) { candidate = c; break; } }

                if (candidate != null)
                {
                    Log($"  module[{m}] matched catalog entry: \"{candidate.DisplayName}\" (guid={mGuid})");
                    DumpValueShapeAndValues(candidate.Scriptable, $"module[{m}].scriptable ({candidate.DisplayName})");
                }
                else
                {
                    Log($"  module[{m}] guid={mGuid} - no matching entry in the {_moduleCandidates.Count}-item module catalog (catalog may need refreshing, or this guid isn't a scriptable the game has loaded right now).");
                }
            }
            Log($"========== END DEEP DUMP: blueprint[{bpIndex}] ==========");
        }

        // Same as DumpBlueprintDeep but for a carried inventory item - added
        // to investigate why ResolvedName (AsString's "?" fallback) fails to
        // resolve for some carried items even though InventoryItem.m_GeneratedData
        // is confirmed present on all 3 - need to see the item's own live
        // shape/values (and whether m_GeneratedData or its m_TemplateGuid is
        // actually null/empty for these) rather than guess at a fix.
        private void DumpInventoryItemDeep(int index)
        {
            var items = GetInventorySnapshot();
            if (index < 0 || index >= items.Count)
            {
                Log($"DumpInventoryItemDeep: bad index {index} (have {items.Count} inventory items).");
                return;
            }

            Log($"========== DEEP DUMP: inventory[{index}] ==========");
            object item = items[index];
            DumpValueShapeAndValues(item, "inventoryItem");

            object generatedData = GetInstanceMemberValue(item, "m_GeneratedData");
            DumpValueShapeAndValues(generatedData, "inventoryItem.m_GeneratedData");

            if (generatedData != null)
            {
                object resolvedName = GetInstanceMemberValue(generatedData, "ResolvedName");
                Log($"  ResolvedName raw value = {DescribeValue(resolvedName)} (type: {(resolvedName == null ? "null" : resolvedName.GetType().FullName)})");
            }

            int moduleCount = GetModuleCount(generatedData);
            Log($"  module count (m_Modules.Length): {moduleCount}");

            if (_moduleCandidates.Count == 0) RefreshModuleCandidates(false);

            for (int m = 0; m < moduleCount; m++)
            {
                object module = GetModuleAt(generatedData, m);
                Log($"---------- module[{m}] ----------");
                DumpValueShapeAndValues(module, $"module[{m}]");
            }
            Log($"========== END DEEP DUMP: inventory[{index}] ==========");
        }

        // Prints every field and property (public + nonpublic) on obj, along
        // with its value where it's a simple/printable type (numbers, strings,
        // bools, enums, IntPtr). Complex/object-typed members just print their
        // type name to avoid runaway recursion - call this again on that member
        // directly (e.g. from DumpBlueprintDeep) if you need to go a level deeper.
        private void DumpValueShapeAndValues(object obj, string label)
        {
            if (obj == null) { Log($"  {label} = null"); return; }
            var t = obj.GetType();
            var flags = BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Instance;
            Log($"  {label} : {t.FullName}");

            try
            {
                foreach (var f in t.GetFields(flags))
                    Log($"    [field] {f.FieldType.Name} {f.Name} = {DescribeValue(SafeGet(() => f.GetValue(obj)))}");
            }
            catch (Exception ex) { Log("    GetFields threw: " + ex.Message); }

            try
            {
                foreach (var p in t.GetProperties(flags))
                {
                    if (p.GetIndexParameters().Length > 0)
                    {
                        Log($"    [prop]  {p.PropertyType.Name} {p.Name}[..] (indexed - skipped, needs an explicit index)");
                        continue;
                    }
                    Log($"    [prop]  {p.PropertyType.Name} {p.Name} = {DescribeValue(SafeGet(() => p.GetValue(obj)))}");
                }
            }
            catch (Exception ex) { Log("    GetProperties threw: " + ex.Message); }

            try
            {
                var methodSigs = new List<string>();
                foreach (var mi in t.GetMethods(flags))
                    methodSigs.Add($"{mi.ReturnType.Name} {mi.Name}({mi.GetParameters().Length})");
                Log($"    [methods] {string.Join(", ", methodSigs)}");
            }
            catch (Exception ex) { Log("    GetMethods threw: " + ex.Message); }
        }

        private static object SafeGet(Func<object> getter)
        {
            try { return getter(); }
            catch (Exception ex) { return "<threw: " + ex.Message + ">"; }
        }

        private static string DescribeValue(object val)
        {
            if (val == null) return "null";
            if (val is string) return "\"" + val + "\"";
            var vt = val.GetType();
            if (vt.IsEnum || vt.IsPrimitive || val is IntPtr) return val.ToString();
            return "<" + vt.Name + ">";
        }

        // ---------- module helpers ----------

        private int GetModuleCount(object generatedData)
        {
            object modules = GetInstanceMemberValue(generatedData, "m_Modules");
            if (modules == null) return 0;
            var lengthProp = modules.GetType().GetProperty("Length", BindingFlags.Public | BindingFlags.Instance);
            if (lengthProp == null) return 0;
            try { return (int)lengthProp.GetValue(modules); }
            catch { return 0; }
        }

        private object GetModuleAt(object generatedData, int index)
        {
            object modules = GetInstanceMemberValue(generatedData, "m_Modules");
            if (modules == null) return null;
            var itemProp = modules.GetType().GetProperty("Item", BindingFlags.Public | BindingFlags.Instance);
            if (itemProp == null) return null;
            try { return itemProp.GetValue(modules, new object[] { index }); }
            catch { return null; }
        }

        // Same three helpers as GetModuleCount/GetModuleAt/TryWriteModuleBack,
        // just pointed at GeneratedItem.m_Cosmetics (CosmeticSelection[])
        // instead of m_Modules.
        private int GetCosmeticCount(object generatedData)
        {
            object cosmetics = GetInstanceMemberValue(generatedData, "m_Cosmetics");
            if (cosmetics == null) return 0;
            var lengthProp = cosmetics.GetType().GetProperty("Length", BindingFlags.Public | BindingFlags.Instance);
            if (lengthProp == null) return 0;
            try { return (int)lengthProp.GetValue(cosmetics); }
            catch { return 0; }
        }

        private object GetCosmeticAt(object generatedData, int index)
        {
            object cosmetics = GetInstanceMemberValue(generatedData, "m_Cosmetics");
            if (cosmetics == null) return null;
            var itemProp = cosmetics.GetType().GetProperty("Item", BindingFlags.Public | BindingFlags.Instance);
            if (itemProp == null) return null;
            try { return itemProp.GetValue(cosmetics, new object[] { index }); }
            catch { return null; }
        }

        private bool TryWriteCosmeticBack(object generatedData, int cosmeticIndex, object mutatedCosmetic)
        {
            object cosmetics = GetInstanceMemberValue(generatedData, "m_Cosmetics");
            if (cosmetics == null) { Log("TryWriteCosmeticBack: m_Cosmetics is null."); return false; }
            var itemProp = cosmetics.GetType().GetProperty("Item", BindingFlags.Public | BindingFlags.Instance);
            if (itemProp == null) { Log("TryWriteCosmeticBack: m_Cosmetics has no Item property."); return false; }
            if (!itemProp.CanWrite) { Log("TryWriteCosmeticBack: m_Cosmetics.Item has no setter (CanWrite=false) - array type " + cosmetics.GetType().FullName + "."); return false; }
            try { itemProp.SetValue(cosmetics, mutatedCosmetic, new object[] { cosmeticIndex }); return true; }
            catch (Exception ex) { Log($"TryWriteCosmeticBack: set_Item({cosmeticIndex}) threw: {ex.Message}"); return false; }
        }

        // Turrets/guns/reactors/shields/etc. each have SOME number of fixed
        // "Upgradeable Features" (basic) module slots plus a rarity-scaled
        // number of "Custom Modules" slots. IMPORTANT: the basic-slot COUNT
        // is NOT the same for every item type - confirmed Reactors have 1
        // basic slot (weapons have 2).
        //
        // CORRECTED (previous version of this comment/fix was wrong): a real
        // log (Editor_Log shields fix.txt) proved
        // ItemGenerator.GetModuleCount(ItemRarity) returns EXACTLY the same
        // numbers as this flat table below (Common=0, Rare=1, Epic=2,
        // Legendary=3) - it's the CUSTOM slot count directly, not a
        // basic+custom total, and it's identical for every category. The
        // previous fix treated it as a total and subtracted this item's own
        // basic count from it, which UNDER-counted custom slots on anything
        // with basic slots (weapons/reactors lost basicCount worth of custom
        // slots they used to correctly get) while never actually fixing the
        // original complaint either (items with 0 basic slots, like
        // Shields, still landed on the same 2-at-Epic as the flat table
        // always gave, since officialTotal - 0 = officialTotal).
        //
        // Per Cameron, purple (Epic) Shield Generators specifically need 3
        // custom modules - one more than the generic per-rarity value (2).
        // Shields have 0 basic/Upgradeable Features slots at all, so this
        // isn't explainable by a basic-slot deduction - it's a genuine,
        // hardcoded category-specific bonus the real game applies that
        // GetModuleCount(rarity) alone can't reveal (that call takes no
        // category argument). IsShieldCategory below detects Shield
        // Generators items (same name/category lookup BuildBlueprintsJson
        // uses) and adds +1 custom slot on top of the generic value. Only
        // Epic is confirmed by Cameron; the +1 is applied at every rarity as
        // the most likely consistent pattern - flag it if any other Shield
        // rarity still looks off in-game.
        private static readonly Dictionary<string, int> CustomModuleCountByRarity =
            new Dictionary<string, int>(StringComparer.OrdinalIgnoreCase)
            {
                { "Common", 0 }, { "Rare", 1 }, { "Epic", 2 }, { "Legendary", 3 }
            };
        // Only used if we can't resolve ANY module's basic/custom kind on an
        // item at all (module catalog not loaded yet, etc) - last resort.
        private const int FallbackBasicModuleCount = 2;

        // Official ItemGenerator.GetModuleCount(ItemRarity) - the real
        // CUSTOM slot count for a rarity (confirmed identical to the flat
        // table above via a real log, NOT a basic+custom total - see the
        // comment above CustomModuleCountByRarity). Returns -1 if the
        // method/type can't be found or the call throws, so callers can fall
        // back to the flat-table guess.
        private int GetOfficialCustomModuleCount(object rarityValue)
        {
            if (rarityValue == null) return -1;
            if (_itemGeneratorType == null) _itemGeneratorType = FindType("Il2CppKeepsake.GeneratedItems.ItemGenerator");
            if (_itemGeneratorType == null) return -1;
            var method = _itemGeneratorType.GetMethod("GetModuleCount", BindingFlags.Public | BindingFlags.Static);
            if (method == null) return -1;
            try
            {
                object result = method.Invoke(null, new object[] { rarityValue });
                return result is int i ? i : -1;
            }
            catch (Exception ex)
            {
                Log("GetOfficialCustomModuleCount: ItemGenerator.GetModuleCount threw: " + ex.Message);
                return -1;
            }
        }

        // Shield Generators get a confirmed +1 custom module bonus over the
        // generic per-rarity value (see comment above
        // CustomModuleCountByRarity). Real owned-item names confirmed via a
        // "Dump Module Kinds" log include Microsoft(tm) Defender, Fighter
        // Shield, Skirmisher Shield, and Fortress Shield - i.e. there are
        // several distinct Shield templates, NOT just one, so this checks
        // the item's own m_CategoryGuid against the confirmed Shield
        // Generators category guid FIRST (same guid-keyed CategoryByGuid
        // map BuildBlueprintsJson uses - catches every shield automatically,
        // present or future, without needing every name hardcoded). Only
        // falls back to the template-guid -> original-name ->
        // KnownItemCategory name lookup when no blueprint wrapper is
        // available to read a category guid off of (e.g. called from an
        // inventory-item context, which has no category system at all -
        // moot in practice since Shields aren't carried inventory items).
        private const string ShieldGeneratorsCategoryGuid = "1292627bbf531c84ba2c56e6e55af6d3";
        private bool IsShieldCategory(object generatedData, object bp)
        {
            if (bp != null)
            {
                string categoryGuid = GetInstanceMemberValue(bp, "m_CategoryGuid") as string;
                if (categoryGuid != null)
                    return string.Equals(categoryGuid, ShieldGeneratorsCategoryGuid, StringComparison.OrdinalIgnoreCase);
            }
            string templateGuid = GetInstanceMemberValue(generatedData, "m_TemplateGuid") as string;
            if (templateGuid == null) return false;
            if (_templateOriginalNames.Count == 0) RefreshTemplateOriginalNames();
            if (!_templateOriginalNames.TryGetValue(templateGuid, out var originalName)) return false;
            return KnownItemCategory.TryGetValue(originalName, out var category)
                && string.Equals(category, "Shield Generators", StringComparison.OrdinalIgnoreCase);
        }

        private ModuleCandidate FindCandidateByGuid(string guid)
        {
            if (string.IsNullOrEmpty(guid)) return null;
            foreach (var c in _moduleCandidates) if (c.Guid == guid) return c;
            return null;
        }

        // Adds/removes custom module slots on generatedData.m_Modules to match
        // the target rarity's custom-slot count, on top of however many basic
        // ("Upgradeable Features") slots THIS item actually has (read from its
        // own current modules, not assumed). Mutates generatedData in place;
        // the caller is responsible for writing generatedData back onto its
        // parent blueprint afterward (same as the rarity write-back).
        // `bp` (optional) is the owning blueprint wrapper, used only to read
        // m_CategoryGuid for the Shield Generators bonus check
        // (IsShieldCategory) - pass null from inventory-item call sites,
        // which have no category system at all.
        private void ResizeModulesForRarity(object generatedData, string rarityName, object rarityValue, object bp = null)
        {
            object modules = GetInstanceMemberValue(generatedData, "m_Modules");
            if (modules == null) { Log("ResizeModulesForRarity: m_Modules is null, skipping."); return; }

            var lengthProp = modules.GetType().GetProperty("Length", BindingFlags.Public | BindingFlags.Instance);
            var itemProp = modules.GetType().GetProperty("Item", BindingFlags.Public | BindingFlags.Instance);
            if (lengthProp == null || itemProp == null) { Log("ResizeModulesForRarity: m_Modules missing Length/Item, skipping."); return; }

            int currentCount;
            try { currentCount = (int)lengthProp.GetValue(modules); }
            catch (Exception ex) { Log("ResizeModulesForRarity: reading Length threw: " + ex.Message); return; }

            if (currentCount == 0)
            {
                Log("ResizeModulesForRarity: item has 0 modules - doesn't look like a turret/gun/reactor, leaving module count untouched.");
                return;
            }

            if (_moduleCandidates.Count == 0) RefreshModuleCandidates(false);

            // How many of THIS item's CURRENT modules are basic
            // ("Upgradeable Features")? Read directly off the item instead
            // of assuming a constant - this is what actually varies by item
            // type (see comment on CustomModuleCountByRarity above).
            int basicCount = 0;
            int resolvedCount = 0;
            for (int bi = 0; bi < currentCount; bi++)
            {
                object element;
                try { element = itemProp.GetValue(modules, new object[] { bi }); } catch { continue; }
                var cand = FindCandidateByGuid(GetInstanceMemberValue(element, "m_ModuleGuid") as string);
                if (cand == null) continue;
                resolvedCount++;
                if (cand.IsBasicModule) basicCount++;
            }
            if (resolvedCount == 0)
            {
                basicCount = Math.Min(FallbackBasicModuleCount, currentCount);
                Log($"ResizeModulesForRarity: could not resolve any module's basic/custom kind (module catalog not loaded?) - falling back to assuming {basicCount} basic slot(s).");
            }

            // "Upgradeable Features" don't have their own independently-set
            // rarity in the real game at all - they just always match the
            // item's own rarity (confirmed: there's no rarity control for
            // them in the assembler UI). So every time the item's rarity is
            // touched, stamp that same rarity onto every currently-resolved
            // basic module too - in place, on the array that's already live,
            // so this still happens even below where module COUNT doesn't
            // change (the early-return case right after this).
            int basicRaritySynced = 0;
            for (int bi = 0; bi < currentCount; bi++)
            {
                object element;
                try { element = itemProp.GetValue(modules, new object[] { bi }); } catch { continue; }
                var cand = FindCandidateByGuid(GetInstanceMemberValue(element, "m_ModuleGuid") as string);
                bool isBasic = cand != null ? cand.IsBasicModule : (resolvedCount == 0 && bi < basicCount);
                if (!isBasic) continue;
                if (TrySetInstanceMemberValue(element, "m_Rarity", rarityValue))
                {
                    try { itemProp.SetValue(modules, element, new object[] { bi }); basicRaritySynced++; }
                    catch (Exception ex) { Log($"ResizeModulesForRarity: writing synced rarity into slot {bi} threw: " + ex.Message); }
                }
            }
            if (basicRaritySynced > 0)
                Log($"ResizeModulesForRarity: synced {basicRaritySynced} basic module rarity value(s) to '{rarityName}' (Upgradeable Features always match item rarity).");

            // Prefer the official per-rarity CUSTOM count straight from the
            // game's own ItemGenerator.GetModuleCount(rarity) (confirmed to
            // return the custom count directly, not a total - see the
            // comment above CustomModuleCountByRarity); only fall back to
            // the flat table below if that call isn't available for some
            // reason. Either way, Shield Generators get a confirmed +1
            // custom-slot bonus on top (see IsShieldCategory).
            int officialCustom = GetOfficialCustomModuleCount(rarityValue);
            bool isShield = IsShieldCategory(generatedData, bp);
            int targetCount;
            int customCount;
            if (officialCustom >= 0)
            {
                customCount = officialCustom;
                if (isShield) customCount += 1;
                targetCount = basicCount + customCount;
                Log($"ResizeModulesForRarity: ItemGenerator.GetModuleCount('{rarityName}') = {officialCustom} custom slot(s) (generic){(isShield ? $", +1 Shield Generators bonus -> {customCount}" : "")}; this item has {basicCount} basic -> {customCount} custom, {targetCount} total.");
            }
            else if (CustomModuleCountByRarity.TryGetValue(rarityName ?? "", out int fallbackCustomCount))
            {
                customCount = fallbackCustomCount;
                if (isShield) customCount += 1;
                targetCount = basicCount + customCount;
                Log($"ResizeModulesForRarity: official GetModuleCount unavailable - falling back to the flat per-rarity table ({customCount} custom{(isShield ? ", includes +1 Shield Generators bonus" : "")}).");
            }
            else
            {
                Log($"ResizeModulesForRarity: unrecognized rarity '{rarityName}' and official GetModuleCount unavailable - skipping module count adjustment.");
                return;
            }

            if (currentCount == targetCount)
            {
                Log($"ResizeModulesForRarity: already at {currentCount} module(s) ({basicCount} basic) for '{rarityName}', nothing to do.");
                return;
            }

            object newArray;
            try { newArray = Activator.CreateInstance(modules.GetType(), new object[] { targetCount }); }
            catch (Exception ex) { Log("ResizeModulesForRarity: could not allocate a new m_Modules array (" + modules.GetType().FullName + "): " + ex.Message); return; }

            int copyCount = Math.Min(currentCount, targetCount);
            object templateModule = null;
            for (int i = 0; i < copyCount; i++)
            {
                object element;
                try { element = itemProp.GetValue(modules, new object[] { i }); }
                catch (Exception ex) { Log($"ResizeModulesForRarity: reading module[{i}] threw: " + ex.Message); return; }
                if (i == 0) templateModule = element;
                try { itemProp.SetValue(newArray, element, new object[] { i }); }
                catch (Exception ex) { Log($"ResizeModulesForRarity: copying module[{i}] into new array threw: " + ex.Message); return; }
            }

            if (targetCount > currentCount)
            {
                if (templateModule == null) { try { templateModule = itemProp.GetValue(modules, new object[] { 0 }); } catch { } }
                Type moduleType = templateModule?.GetType();

                // Every slot ResizeModulesForRarity ever ADDS is, by
                // definition, past the fixed Upgradeable Features count -
                // i.e. it must be a genuine "Custom Module" (m_IsBasicModule
                // = false) or the game will show it under the wrong section
                // (this was the actual bug: the old code cloned slot 0,
                // which is a basic/upgradeable module type).
                if (_moduleCandidates.Count == 0) RefreshModuleCandidates(false);
                string itemTemplateGuid = GetInstanceMemberValue(generatedData, "m_TemplateGuid") as string;
                var pool = BuildCustomModulePool(rarityName, itemTemplateGuid);

                for (int i = currentCount; i < targetCount; i++)
                {
                    object newModule = null;
                    if (moduleType != null && pool.Count > 0)
                    {
                        var picked = PickWeightedRandomCandidate(pool, _rerollRng);
                        if (picked != null) newModule = BuildRerolledModule(moduleType, picked, rarityValue, _rerollRng);
                    }
                    if (newModule == null && moduleType != null)
                    {
                        // Last-resort fallback so a new slot is never left
                        // completely broken: clone whatever's already
                        // equipped. May land in the wrong in-game section if
                        // that happens to be a basic module - logged so it's
                        // visible when it happens.
                        string fallbackGuid = templateModule == null ? null : GetInstanceMemberValue(templateModule, "m_ModuleGuid") as string;
                        newModule = BuildNewModule(moduleType, fallbackGuid, rarityValue);
                        if (newModule != null) Log($"ResizeModulesForRarity: no compatible custom-module candidate found for slot {i} - fell back to cloning the existing module type (may show under the wrong section in-game).");
                    }
                    if (newModule == null) { Log($"ResizeModulesForRarity: could not construct a new module for slot {i}, leaving it default."); continue; }
                    try { itemProp.SetValue(newArray, newModule, new object[] { i }); }
                    catch (Exception ex) { Log($"ResizeModulesForRarity: writing new module into slot {i} threw: " + ex.Message); }
                }
            }

            bool wroteArrayBack = TrySetInstanceMemberValue(generatedData, "m_Modules", newArray);
            Log($"ResizeModulesForRarity: {currentCount} -> {targetCount} module(s) ({basicCount} basic + {customCount} custom) for rarity '{rarityName}', m_Modules write-back={wroteArrayBack}.");
        }

        // Called right after HandleChangeItemTemplate changes m_TemplateGuid -
        // every existing module slot was picked/validated against the OLD
        // template's allow/deny lists, so rebuild each slot from scratch
        // against the NEW template rather than just resizing the count (which
        // is all ResizeModulesForRarity does). Preserves each slot's own
        // rarity and upgrade level, and its basic/custom kind (so it doesn't
        // jump to the wrong in-game section) - only the module TYPE itself
        // changes, and only for slots that actually need it (a module with no
        // allow-list at all is compatible with everything and is left alone).
        private void RebuildModulesForNewTemplate(object generatedData, string newTemplateGuid)
        {
            object modules = GetInstanceMemberValue(generatedData, "m_Modules");
            if (modules == null) { Log("RebuildModulesForNewTemplate: m_Modules is null, skipping."); return; }

            var lengthProp = modules.GetType().GetProperty("Length", BindingFlags.Public | BindingFlags.Instance);
            var itemProp = modules.GetType().GetProperty("Item", BindingFlags.Public | BindingFlags.Instance);
            if (lengthProp == null || itemProp == null) { Log("RebuildModulesForNewTemplate: m_Modules missing Length/Item, skipping."); return; }

            int count;
            try { count = (int)lengthProp.GetValue(modules); }
            catch (Exception ex) { Log("RebuildModulesForNewTemplate: reading Length threw: " + ex.Message); return; }
            if (count == 0) return;

            if (_moduleCandidates.Count == 0) RefreshModuleCandidates(false);

            for (int i = 0; i < count; i++)
            {
                object existing;
                try { existing = itemProp.GetValue(modules, new object[] { i }); }
                catch (Exception ex) { Log($"RebuildModulesForNewTemplate: reading module[{i}] threw: " + ex.Message); continue; }
                if (existing == null) continue;

                Type moduleType = existing.GetType();
                string existingGuid = GetInstanceMemberValue(existing, "m_ModuleGuid") as string;
                var existingCandidate = FindCandidateByGuid(existingGuid);

                if (existingCandidate != null && IsTemplateCompatible(existingCandidate, newTemplateGuid))
                {
                    Log($"RebuildModulesForNewTemplate: slot {i} ('{existingCandidate.DisplayName}') is already compatible with the new template - left as-is.");
                    continue;
                }

                bool wantBasic = existingCandidate?.IsBasicModule ?? (i < FallbackBasicModuleCount);
                object moduleRarity = GetInstanceMemberValue(existing, "m_Rarity");
                string moduleRarityName = moduleRarity?.ToString();
                int upgradeLevel = SafeInt(GetInstanceMemberValue(existing, "m_UpgradeLevel"));

                var byRarity = new List<ModuleCandidate>();
                foreach (var c in _moduleCandidates) if (IsRarityWithinRange(c.Scriptable, moduleRarityName)) byRarity.Add(c);
                if (byRarity.Count == 0) byRarity.AddRange(_moduleCandidates);

                var byTemplate = new List<ModuleCandidate>();
                foreach (var c in byRarity) if (IsTemplateCompatible(c, newTemplateGuid)) byTemplate.Add(c);
                if (byTemplate.Count == 0) byTemplate.AddRange(byRarity);

                var byKind = new List<ModuleCandidate>();
                foreach (var c in byTemplate) if (c.IsBasicModule == wantBasic) byKind.Add(c);
                if (byKind.Count == 0) byKind.AddRange(byTemplate);

                if (byKind.Count == 0) { Log($"RebuildModulesForNewTemplate: no module candidates loaded at all - leaving slot {i} untouched."); continue; }

                var picked = PickWeightedRandomCandidate(byKind, _rerollRng);
                if (picked == null) continue;

                object newModule = BuildRerolledModule(moduleType, picked, moduleRarity, _rerollRng);
                if (newModule == null) { Log($"RebuildModulesForNewTemplate: could not construct replacement for slot {i}."); continue; }
                TrySetInstanceMemberValue(newModule, "m_UpgradeLevel", upgradeLevel);

                try { itemProp.SetValue(modules, newModule, new object[] { i }); }
                catch (Exception ex) { Log($"RebuildModulesForNewTemplate: writing replacement into slot {i} threw: " + ex.Message); continue; }

                Log($"RebuildModulesForNewTemplate: slot {i} '{existingCandidate?.DisplayName ?? existingGuid ?? "?"}' -> '{picked.DisplayName}' (kept rarity={moduleRarityName}, level={upgradeLevel}).");
            }

            TrySetInstanceMemberValue(generatedData, "m_Modules", modules);
        }

        // Candidate pool for a brand-new "Custom Modules" slot: non-basic
        // (m_IsBasicModule=false, so the game files it in the right section),
        // rarity-compatible, and item-template-compatible - each stage falls
        // back to the previous, wider stage if it comes up empty, so this
        // never returns zero candidates as long as ANY module type is loaded
        // at all.
        private List<ModuleCandidate> BuildCustomModulePool(string rarityName, string itemTemplateGuid)
        {
            var byKind = new List<ModuleCandidate>();
            foreach (var c in _moduleCandidates) if (!c.IsBasicModule) byKind.Add(c);
            if (byKind.Count == 0) byKind.AddRange(_moduleCandidates);

            var byRarity = new List<ModuleCandidate>();
            foreach (var c in byKind) if (IsRarityWithinRange(c.Scriptable, rarityName)) byRarity.Add(c);
            if (byRarity.Count == 0) byRarity.AddRange(byKind);

            var byTemplate = new List<ModuleCandidate>();
            foreach (var c in byRarity) if (IsTemplateCompatible(c, itemTemplateGuid)) byTemplate.Add(c);
            if (byTemplate.Count == 0) byTemplate.AddRange(byRarity);

            return byTemplate;
        }

        // LAST-RESORT fallback only (see BuildCustomModulePool/BuildRerolledModule,
        // which handle the normal case): clones the guid of an already-equipped
        // module on this same item, at the item's new rarity, level 0, with a
        // fresh rolls array. Only used when no real non-basic candidate could
        // be found at all - the clone may land in the wrong in-game section
        // since we don't check its m_IsBasicModule here. You can swap it to
        // whatever you actually want afterward via the module type dropdown.
        private object BuildNewModule(Type moduleType, string templateGuid, object rarityValue)
        {
            if (moduleType == null || templateGuid == null) { Log("BuildNewModule: missing moduleType or templateGuid."); return null; }

            object newModule;
            try { newModule = Activator.CreateInstance(moduleType); }
            catch (Exception ex) { Log($"BuildNewModule: Activator.CreateInstance({moduleType.FullName}) threw: {ex.Message}"); return null; }

            if (!TrySetInstanceMemberValue(newModule, "m_ModuleGuid", templateGuid)) return null;
            TrySetInstanceMemberValue(newModule, "m_Rarity", rarityValue);
            TrySetInstanceMemberValue(newModule, "m_UpgradeLevel", 0);

            try
            {
                if (_moduleCandidates.Count == 0) RefreshModuleCandidates(false);
                ModuleCandidate candidate = null;
                foreach (var c in _moduleCandidates) { if (c.Guid == templateGuid) { candidate = c; break; } }
                if (candidate != null)
                {
                    var getTweakables = candidate.Scriptable.GetType().GetMethod("GetTweakableValuesForRarity", BindingFlags.Public | BindingFlags.Instance);
                    int rollCount = 1;
                    if (getTweakables != null)
                    {
                        object list = getTweakables.Invoke(candidate.Scriptable, new object[] { rarityValue });
                        var countProp = list?.GetType().GetProperty("Count", BindingFlags.Public | BindingFlags.Instance);
                        if (countProp != null) rollCount = Math.Max(1, (int)countProp.GetValue(list));
                    }
                    var rollsProp = moduleType.GetProperty("m_BaseValueRolls", BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Instance);
                    if (rollsProp != null)
                    {
                        var arrayType = rollsProp.PropertyType;
                        object newRolls = Activator.CreateInstance(arrayType, new object[] { rollCount });
                        var rollsItemProp = arrayType.GetProperty("Item", BindingFlags.Public | BindingFlags.Instance);
                        if (rollsItemProp != null)
                            for (int i = 0; i < rollCount; i++) rollsItemProp.SetValue(newRolls, 0.5f, new object[] { i });
                        rollsProp.SetValue(newModule, newRolls);
                    }
                }
            }
            catch (Exception ex) { Log("BuildNewModule: rolls setup threw: " + ex.Message); }

            return newModule;
        }

        // ---------- reset-to-original ----------

        private static string ModuleSnapshotKey(string bpGuid, int modIndex) => (bpGuid ?? "?") + "|" + modIndex;

        // Called every time a module is listed (BuildBlueprintsJson) - only
        // actually records anything the first time a given module is seen, so
        // this captures pre-edit state as long as the web UI gets opened/
        // refreshed before you start changing things.
        private void EnsureModuleSnapshot(string bpGuid, int modIndex, object module)
        {
            if (module == null) return;
            string key = ModuleSnapshotKey(bpGuid, modIndex);
            if (_originalModuleSnapshots.ContainsKey(key)) return;
            try
            {
                _originalModuleSnapshots[key] = new ModuleSnapshot
                {
                    ModuleGuid = GetInstanceMemberValue(module, "m_ModuleGuid") as string,
                    Rarity = GetInstanceMemberValue(module, "m_Rarity")?.ToString(),
                    UpgradeLevel = SafeInt(GetInstanceMemberValue(module, "m_UpgradeLevel")),
                    Rolls = ReadFloatArray(GetInstanceMemberValue(module, "m_BaseValueRolls"))
                };
            }
            catch (Exception ex) { Log($"EnsureModuleSnapshot({key}): threw {ex.Message}"); }
        }

        private static string CosmeticSnapshotKey(string bpGuid, int cosmeticIndex) => (bpGuid ?? "?") + "|" + cosmeticIndex;

        // Same "only the first time we ever see it" rule as EnsureModuleSnapshot,
        // called every time a blueprint is listed (BuildBlueprintsJson).
        private void EnsureCosmeticSnapshot(string bpGuid, int cosmeticIndex, string cosmeticGuid)
        {
            if (bpGuid == null) return;
            string key = CosmeticSnapshotKey(bpGuid, cosmeticIndex);
            if (_originalCosmeticSnapshots.ContainsKey(key)) return;
            _originalCosmeticSnapshots[key] = new CosmeticSnapshot { CosmeticGuid = cosmeticGuid };
        }

        // Item-level counterpart to EnsureModuleSnapshot - same "only the
        // first time we ever see it" rule, keyed by blueprint guid alone.
        private void EnsureItemSnapshot(string bpGuid, object rarity, object level, string templateGuid, string consumableGuid = null)
        {
            if (bpGuid == null) return;
            if (_originalItemSnapshots.ContainsKey(bpGuid)) return;
            try
            {
                _originalItemSnapshots[bpGuid] = new ItemSnapshot
                {
                    Rarity = rarity?.ToString(),
                    Level = SafeInt(level),
                    TemplateGuid = templateGuid,
                    ConsumableGuid = consumableGuid
                };
            }
            catch (Exception ex) { Log($"EnsureItemSnapshot({bpGuid}): threw {ex.Message}"); }
        }

        // Currency counterpart - only captures once creditsAmount/ingotAmounts
        // look "real" (see CurrenciesLookReal's reasoning), so a stale
        // all-zero read before a save has loaded never gets locked in as the
        // "original" values.
        private void EnsureCurrencySnapshot(int creditsAmount, List<int> ingotAmounts)
        {
            if (_originalCurrencySnapshot != null) return;
            bool looksReal = creditsAmount > 0;
            if (!looksReal) foreach (var a in ingotAmounts) if (a > 0) { looksReal = true; break; }
            if (!looksReal) return;

            var snap = new Dictionary<string, int> { ["credits"] = creditsAmount };
            for (int i = 0; i < ingotAmounts.Count; i++) snap["ingot" + i] = ingotAmounts[i];
            _originalCurrencySnapshot = snap;
            Log($"EnsureCurrencySnapshot: captured original currencies (credits={creditsAmount}, ingots=[{string.Join(",", ingotAmounts)}]).");
        }

        private static float[] ReadFloatArray(object arr)
        {
            if (arr == null) return Array.Empty<float>();
            try
            {
                var lengthProp = arr.GetType().GetProperty("Length", BindingFlags.Public | BindingFlags.Instance);
                var itemProp = arr.GetType().GetProperty("Item", BindingFlags.Public | BindingFlags.Instance);
                if (lengthProp == null || itemProp == null) return Array.Empty<float>();
                int len = (int)lengthProp.GetValue(arr);
                var result = new float[len];
                for (int i = 0; i < len; i++) result[i] = Convert.ToSingle(itemProp.GetValue(arr, new object[] { i }));
                return result;
            }
            catch { return Array.Empty<float>(); }
        }

        // Writes a captured ModuleSnapshot back onto the live (boxed-copy)
        // module and writes that copy back into m_Modules[modIndex] - same
        // write-back pattern as HandleSetRarity/HandleSwapModule. Caller still
        // needs to write generatedData back onto its blueprint afterward.
        private bool ApplyModuleSnapshot(object generatedData, int modIndex, ModuleSnapshot snap)
        {
            object module = GetModuleAt(generatedData, modIndex);
            if (module == null || snap == null) return false;

            if (_itemRarityType == null) _itemRarityType = FindType("Il2CppKeepsake.GeneratedItems.ItemRarity");
            object rarityValue = null;
            if (_itemRarityType != null && snap.Rarity != null)
            {
                try { rarityValue = Enum.Parse(_itemRarityType, snap.Rarity, true); }
                catch (Exception ex) { Log("ApplyModuleSnapshot: Enum.Parse rarity threw: " + ex.Message); }
            }

            bool ok = true;
            if (snap.ModuleGuid != null) ok &= TrySetInstanceMemberValue(module, "m_ModuleGuid", snap.ModuleGuid);
            if (rarityValue != null) ok &= TrySetInstanceMemberValue(module, "m_Rarity", rarityValue);
            ok &= TrySetInstanceMemberValue(module, "m_UpgradeLevel", snap.UpgradeLevel);

            var rollsProp = module.GetType().GetProperty("m_BaseValueRolls", BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Instance);
            if (rollsProp != null && snap.Rolls != null)
            {
                try
                {
                    var arrayType = rollsProp.PropertyType;
                    object newRolls = Activator.CreateInstance(arrayType, new object[] { snap.Rolls.Length });
                    var itemProp = arrayType.GetProperty("Item", BindingFlags.Public | BindingFlags.Instance);
                    if (itemProp != null)
                        for (int i = 0; i < snap.Rolls.Length; i++) itemProp.SetValue(newRolls, snap.Rolls[i], new object[] { i });
                    rollsProp.SetValue(module, newRolls);
                }
                catch (Exception ex) { Log("ApplyModuleSnapshot: rolls restore threw: " + ex.Message); ok = false; }
            }

            bool wroteModuleBack = TryWriteModuleBack(generatedData, modIndex, module);
            return ok && wroteModuleBack;
        }

        private void HandleResetModule(HttpListenerContext ctx)
        {
            int bpIndex = QueryInt(ctx, "blueprintIndex", -1);
            int modIndex = QueryInt(ctx, "moduleIndex", -1);

            var blueprints = GetBlueprintsSnapshot();
            if (bpIndex < 0 || bpIndex >= blueprints.Count) { WriteJson(ctx, 400, "{\"error\":\"bad blueprintIndex\"}"); return; }
            object bp = blueprints[bpIndex];
            object generatedData = GetInstanceMemberValue(bp, "m_GeneratedData");
            string bpGuid = GetInstanceMemberValue(bp, "m_Guid") as string;

            string key = ModuleSnapshotKey(bpGuid, modIndex);
            if (!_originalModuleSnapshots.TryGetValue(key, out var snap))
            {
                WriteJson(ctx, 400, "{\"error\":\"no original value captured for this module yet - open/refresh the blueprint list once before editing it\"}");
                return;
            }

            bool ok = ApplyModuleSnapshot(generatedData, modIndex, snap);
            bool wroteGeneratedBack = TrySetInstanceMemberValue(bp, "m_GeneratedData", generatedData);
            Log($"HandleResetModule: blueprint[{bpIndex}] module[{modIndex}] reset to original, applySnapshot={ok}, bp.m_GeneratedData wroteBack={wroteGeneratedBack}.");
            if (ok) SaveNow();
            WriteJson(ctx, 200, "{\"ok\":" + (ok ? "true" : "false") + "}");
        }

        private void HandleResetAllModules(HttpListenerContext ctx)
        {
            int bpIndex = QueryInt(ctx, "blueprintIndex", -1);

            var blueprints = GetBlueprintsSnapshot();
            if (bpIndex < 0 || bpIndex >= blueprints.Count) { WriteJson(ctx, 400, "{\"error\":\"bad blueprintIndex\"}"); return; }
            object bp = blueprints[bpIndex];
            object generatedData = GetInstanceMemberValue(bp, "m_GeneratedData");
            string bpGuid = GetInstanceMemberValue(bp, "m_Guid") as string;

            int moduleCount = GetModuleCount(generatedData);
            int resetCount = 0;
            for (int m = 0; m < moduleCount; m++)
            {
                string key = ModuleSnapshotKey(bpGuid, m);
                if (_originalModuleSnapshots.TryGetValue(key, out var snap))
                {
                    if (ApplyModuleSnapshot(generatedData, m, snap)) resetCount++;
                }
            }
            bool wroteGeneratedBack = TrySetInstanceMemberValue(bp, "m_GeneratedData", generatedData);
            Log($"HandleResetAllModules: blueprint[{bpIndex}] reset {resetCount}/{moduleCount} module(s) to original, bp.m_GeneratedData wroteBack={wroteGeneratedBack}.");
            if (resetCount > 0) SaveNow();
            WriteJson(ctx, 200, "{\"ok\":true,\"resetCount\":" + resetCount + ",\"moduleCount\":" + moduleCount + "}");
        }

        // Global "Reset Everything" - every item's rarity/level, every
        // module's guid/rarity/level/rolls, and every currency amount, all
        // back to whatever they were the first time this session saw them
        // (i.e. when you first opened/refreshed the web UI - as close to
        // "when the game was launched" as this mod can actually observe).
        // For each item: restore rarity first, then re-run
        // ResizeModulesForRarity for that SAME original rarity name - this
        // recomputes the correct original module count (basic slots this
        // item actually has + that rarity's custom-slot count) rather than
        // needing to have stored a count separately, so it can't drift out
        // of sync with CustomModuleCountByRarity. Whatever ends up in any
        // newly-(re)created slot from that resize gets overwritten right
        // after by the real per-module snapshot anyway.
        private void HandleResetEverything(HttpListenerContext ctx)
        {
            if (_itemRarityType == null) _itemRarityType = FindType("Il2CppKeepsake.GeneratedItems.ItemRarity");
            var blueprints = GetBlueprintsSnapshot();
            int itemsTouched = 0, modulesReset = 0, cosmeticsReset = 0;

            foreach (var bp in blueprints)
            {
                object generatedData = GetInstanceMemberValue(bp, "m_GeneratedData");
                string bpGuid = GetInstanceMemberValue(bp, "m_Guid") as string;
                bool touched = false;

                if (bpGuid != null && _originalItemSnapshots.TryGetValue(bpGuid, out var itemSnap))
                {
                    if (!string.IsNullOrEmpty(itemSnap.TemplateGuid))
                    {
                        string currentTemplateGuid = GetInstanceMemberValue(generatedData, "m_TemplateGuid") as string;
                        if (currentTemplateGuid != itemSnap.TemplateGuid)
                        {
                            if (TrySetInstanceMemberValue(generatedData, "m_TemplateGuid", itemSnap.TemplateGuid)) touched = true;
                        }
                    }
                    if (itemSnap.Rarity != null && _itemRarityType != null)
                    {
                        object rarityValue = null;
                        try { rarityValue = Enum.Parse(_itemRarityType, itemSnap.Rarity, true); }
                        catch (Exception ex) { Log($"HandleResetEverything: Enum.Parse rarity '{itemSnap.Rarity}' threw: {ex.Message}"); }
                        if (rarityValue != null)
                        {
                            if (TrySetInstanceMemberValue(generatedData, "m_Rarity", rarityValue)) touched = true;
                            ResizeModulesForRarity(generatedData, itemSnap.Rarity, rarityValue, bp);
                        }
                    }
                    if (TrySetInstanceMemberValue(generatedData, "m_Level", itemSnap.Level)) touched = true;
                }

                int moduleCount = GetModuleCount(generatedData);
                for (int m = 0; m < moduleCount; m++)
                {
                    string key = ModuleSnapshotKey(bpGuid, m);
                    if (_originalModuleSnapshots.TryGetValue(key, out var modSnap))
                    {
                        if (ApplyModuleSnapshot(generatedData, m, modSnap)) { modulesReset++; touched = true; }
                    }
                }

                int cosmeticCount = GetCosmeticCount(generatedData);
                for (int c = 0; c < cosmeticCount; c++)
                {
                    string key = CosmeticSnapshotKey(bpGuid, c);
                    if (_originalCosmeticSnapshots.TryGetValue(key, out var cosSnap))
                    {
                        if (ApplyCosmeticSnapshot(generatedData, c, cosSnap)) { cosmeticsReset++; touched = true; }
                    }
                }

                bool wroteGeneratedBack = TrySetInstanceMemberValue(bp, "m_GeneratedData", generatedData);
                if (touched && wroteGeneratedBack) itemsTouched++;
            }

            // Carried inventory items - same snapshot dictionaries, keyed by
            // InvSnapshotKey(index) instead of a blueprint guid. Deliberately
            // NOT resetting m_ResourceAmount/m_AmmoInMag here (by design,
            // matching how currencies are handled as their own separate
            // concern rather than folded into "item" resets).
            var inventoryItems = GetInventorySnapshot();
            var inventoryListRaw = GetInventoryListRaw();
            for (int idx = 0; idx < inventoryItems.Count; idx++)
            {
                object invItem = inventoryItems[idx];
                object invGeneratedData = GetInstanceMemberValue(invItem, "m_GeneratedData");
                string invKey = InvSnapshotKey(idx);
                bool invTouched = false;

                if (_originalItemSnapshots.TryGetValue(invKey, out var invItemSnap))
                {
                    if (!string.IsNullOrEmpty(invItemSnap.TemplateGuid))
                    {
                        string currentTemplateGuid = GetInstanceMemberValue(invGeneratedData, "m_TemplateGuid") as string;
                        if (currentTemplateGuid != invItemSnap.TemplateGuid)
                        {
                            if (TrySetInstanceMemberValue(invGeneratedData, "m_TemplateGuid", invItemSnap.TemplateGuid)) invTouched = true;
                        }
                    }
                    // Consumable swap undo (Change Consumable) - m_GUID lives
                    // on the InventoryItem itself, not m_GeneratedData, since
                    // that's the field that actually identifies a consumable
                    // (see HandleSwapConsumable).
                    if (!string.IsNullOrEmpty(invItemSnap.ConsumableGuid))
                    {
                        string currentConsumableGuid = GetInstanceMemberValue(invItem, "m_GUID") as string;
                        if (currentConsumableGuid != invItemSnap.ConsumableGuid)
                        {
                            if (TrySetInstanceMemberValue(invItem, "m_GUID", invItemSnap.ConsumableGuid)) invTouched = true;
                        }
                    }
                    if (invItemSnap.Rarity != null && _itemRarityType != null)
                    {
                        object rarityValue = null;
                        try { rarityValue = Enum.Parse(_itemRarityType, invItemSnap.Rarity, true); }
                        catch (Exception ex) { Log($"HandleResetEverything: inventory Enum.Parse rarity '{invItemSnap.Rarity}' threw: {ex.Message}"); }
                        if (rarityValue != null)
                        {
                            if (TrySetInstanceMemberValue(invGeneratedData, "m_Rarity", rarityValue)) invTouched = true;
                            ResizeModulesForRarity(invGeneratedData, invItemSnap.Rarity, rarityValue);
                        }
                    }
                    if (TrySetInstanceMemberValue(invGeneratedData, "m_Level", invItemSnap.Level)) invTouched = true;
                }

                int invModuleCount = GetModuleCount(invGeneratedData);
                for (int m = 0; m < invModuleCount; m++)
                {
                    string key = ModuleSnapshotKey(invKey, m);
                    if (_originalModuleSnapshots.TryGetValue(key, out var modSnap))
                    {
                        if (ApplyModuleSnapshot(invGeneratedData, m, modSnap)) { modulesReset++; invTouched = true; }
                    }
                }

                int invCosmeticCount = GetCosmeticCount(invGeneratedData);
                for (int c = 0; c < invCosmeticCount; c++)
                {
                    string key = CosmeticSnapshotKey(invKey, c);
                    if (_originalCosmeticSnapshots.TryGetValue(key, out var cosSnap))
                    {
                        if (ApplyCosmeticSnapshot(invGeneratedData, c, cosSnap)) { cosmeticsReset++; invTouched = true; }
                    }
                }

                bool wroteInvGeneratedBack = TrySetInstanceMemberValue(invItem, "m_GeneratedData", invGeneratedData);
                bool wroteInvListBack = wroteInvGeneratedBack && TryWriteListItemBack(inventoryListRaw, idx, invItem);
                if (invTouched && wroteInvListBack) itemsTouched++;
            }
            // One push after the loop rather than per-item - inventoryListRaw
            // is the same live list object across every iteration, and
            // SetPlayerPersistentInventory takes the whole list anyway, so
            // there's nothing gained by pushing on every single item.
            if (itemsTouched > 0) PushInventoryLive(inventoryListRaw);

            int currenciesReset = 0;
            if (_originalCurrencySnapshot != null && _mgrType != null)
            {
                var setCurrencyMethod = _mgrType.GetMethod("SetCurrency", BindingFlags.Public | BindingFlags.Static);
                if (setCurrencyMethod != null)
                {
                    if (_originalCurrencySnapshot.TryGetValue("credits", out int origCredits))
                    {
                        var prop = _mgrType.GetProperty("CreditsCurrency", BindingFlags.Public | BindingFlags.Static);
                        object creditsCurrency = prop?.GetValue(null);
                        if (creditsCurrency != null)
                        {
                            try { setCurrencyMethod.Invoke(null, new object[] { creditsCurrency, origCredits }); currenciesReset++; }
                            catch (Exception ex) { Log("HandleResetEverything: restoring credits threw: " + ex.Message); }
                        }
                    }
                    var ingots = GetIngotCurrencies();
                    for (int i = 0; i < ingots.Count; i++)
                    {
                        if (_originalCurrencySnapshot.TryGetValue("ingot" + i, out int origAmt))
                        {
                            try { setCurrencyMethod.Invoke(null, new object[] { ingots[i], origAmt }); currenciesReset++; }
                            catch (Exception ex) { Log($"HandleResetEverything: restoring ingot[{i}] threw: " + ex.Message); }
                        }
                    }
                }
            }

            Log($"HandleResetEverything: reset {itemsTouched} item(s) (of {blueprints.Count}), {modulesReset} module(s), {cosmeticsReset} cosmetic(s), {currenciesReset} currency value(s) back to session-start values.");
            if (itemsTouched > 0 || modulesReset > 0 || cosmeticsReset > 0 || currenciesReset > 0) SaveNow();
            WriteJson(ctx, 200, "{\"ok\":true,\"itemsTouched\":" + itemsTouched + ",\"modulesReset\":" + modulesReset + ",\"cosmeticsReset\":" + cosmeticsReset + ",\"currenciesReset\":" + currenciesReset + "}");
        }

        // ---------- reroll (follows the game's own weighting where we can call it directly) ----------

        // ItemModuleScriptable's own m_MinRarity/m_MaxRarity (already shown in
        // the UI as the "range: X-Y" tag). Fails OPEN (returns true) on any
        // error - a broken compatibility check should never silently exclude
        // every candidate and break reroll entirely.
        private bool IsRarityWithinRange(object scriptable, string rarityName)
        {
            if (rarityName == null || scriptable == null) return true;
            try
            {
                object min = GetInstanceMemberValue(scriptable, "m_MinRarity");
                object max = GetInstanceMemberValue(scriptable, "m_MaxRarity");
                if (min == null || max == null || _itemRarityType == null) return true;
                object target = Enum.Parse(_itemRarityType, rarityName, true);
                int minOrd = Convert.ToInt32(min), maxOrd = Convert.ToInt32(max), targetOrd = Convert.ToInt32(target);
                return targetOrd >= minOrd && targetOrd <= maxOrd;
            }
            catch { return true; }
        }

        // AssetReference.m_AssetGUID values, e.g. m_AllowedItems/m_ForbiddenItems
        // on ItemModuleScriptable. These are item TEMPLATE guids (confirmed to
        // match GeneratedItem.m_TemplateGuid, e.g. Sector Scanner's template
        // guid showing up inside Acid Injector's m_ForbiddenItems) - this is
        // how the game restricts a module to specific weapons/components
        // (ship weapon vs on-foot gun, etc.) rather than a simple boolean.
        private List<string> ReadAssetReferenceGuids(object assetReferenceList)
        {
            var result = new List<string>();
            if (assetReferenceList == null) return result;
            try
            {
                foreach (var item in ReadIndexedCollection(assetReferenceList))
                {
                    string g = GetInstanceMemberValue(item, "m_AssetGUID") as string;
                    if (string.IsNullOrEmpty(g)) g = GetInstanceMemberValue(item, "AssetGUID") as string;
                    if (!string.IsNullOrEmpty(g)) result.Add(g);
                }
            }
            catch (Exception ex) { Log("ReadAssetReferenceGuids: threw: " + ex.Message); }
            return result;
        }

        // compatible = (no allow-list, or template is on it) AND template is
        // not on the deny-list. Fails OPEN (returns true) when we don't have
        // a template guid to check against, or on any error - a broken
        // compatibility check should never silently hide every option.
        private bool IsTemplateCompatible(ModuleCandidate c, string templateGuid)
        {
            if (c == null) return true;
            if (string.IsNullOrEmpty(templateGuid)) return true;
            try
            {
                if (c.ForbiddenTemplateGuids != null && c.ForbiddenTemplateGuids.Contains(templateGuid)) return false;
                if (c.AllowedTemplateGuids != null && c.AllowedTemplateGuids.Count > 0 && !c.AllowedTemplateGuids.Contains(templateGuid)) return false;
                return true;
            }
            catch { return true; }
        }

        private float GetModuleSelectionWeight(object scriptable)
        {
            try
            {
                var prop = scriptable.GetType().GetProperty("m_Weight", BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Instance);
                object val = prop?.GetValue(scriptable);
                return val == null ? 1f : Convert.ToSingle(val);
            }
            catch { return 1f; }
        }

        // Weighted-random pick using each candidate's own m_Weight - the same
        // field the game's own module selection uses (confirmed on the
        // "Improved damage" sample dump earlier: m_Weight = 0.33).
        private ModuleCandidate PickWeightedRandomCandidate(List<ModuleCandidate> candidates, Random rng)
        {
            if (candidates == null || candidates.Count == 0) return null;
            var weights = new float[candidates.Count];
            float total = 0f;
            for (int i = 0; i < candidates.Count; i++)
            {
                float w = GetModuleSelectionWeight(candidates[i].Scriptable);
                weights[i] = w > 0f ? w : 0.0001f; // keep zero-weight modules technically reachable rather than dividing by zero
                total += weights[i];
            }
            double roll = rng.NextDouble() * total;
            double cum = 0;
            for (int i = 0; i < candidates.Count; i++)
            {
                cum += weights[i];
                if (roll < cum) return candidates[i];
            }
            return candidates[candidates.Count - 1];
        }

        // Rolls a module rarity the same way the game weights them for an item
        // of a given overall rarity, by calling ItemGenerator's own
        // GetModuleWeightsForItem/GetModuleWeight directly (real weight
        // numbers, no guessing) and doing the actual random draw ourselves.
        // Falls back to the item's own rarity if any part of this isn't
        // available - a failed "authentic" roll should never block reroll.
        private object RollModuleRarity(object itemRarityValue, Random rng)
        {
            object fallback = itemRarityValue;
            try
            {
                if (_itemGeneratorType == null) _itemGeneratorType = FindType("Il2CppKeepsake.GeneratedItems.ItemGenerator");
                if (_itemGeneratorType == null || _itemRarityType == null || itemRarityValue == null) return fallback;

                var configProp = _itemGeneratorType.GetProperty("GenerationConfig", BindingFlags.Public | BindingFlags.Static);
                object config = configProp?.GetValue(null);
                var weightsForItemMethod = _itemGeneratorType.GetMethod("GetModuleWeightsForItem", BindingFlags.Public | BindingFlags.Static);
                var moduleWeightMethod = _itemGeneratorType.GetMethod("GetModuleWeight", BindingFlags.Public | BindingFlags.Static);
                if (config == null || weightsForItemMethod == null || moduleWeightMethod == null)
                {
                    Log("RollModuleRarity: GenerationConfig/GetModuleWeightsForItem/GetModuleWeight not all available - falling back to the item's own rarity.");
                    return fallback;
                }

                object weights = weightsForItemMethod.Invoke(null, new object[] { config, itemRarityValue });
                if (weights == null) return fallback;

                var options = new List<(object value, float weight)>();
                foreach (var rn in new[] { "Common", "Rare", "Epic", "Legendary" })
                {
                    object rv;
                    try { rv = Enum.Parse(_itemRarityType, rn, true); } catch { continue; }
                    float w;
                    try { w = Convert.ToSingle(moduleWeightMethod.Invoke(null, new object[] { weights, rv })); } catch { continue; }
                    if (w > 0f) options.Add((rv, w));
                }
                if (options.Count == 0) return fallback;

                float total = 0f;
                foreach (var o in options) total += o.weight;
                double roll = rng.NextDouble() * total;
                double cum = 0;
                foreach (var o in options)
                {
                    cum += o.weight;
                    if (roll < cum) return o.value;
                }
                return options[options.Count - 1].value;
            }
            catch (Exception ex)
            {
                Log("RollModuleRarity: threw, falling back to the item's own rarity: " + ex.Message);
                return fallback;
            }
        }

        // Rolls an actual value within a tweakable's real Min/Max if we can
        // find those on it (heuristic: any float/double/int property whose
        // name contains "min"/"max"), dumping its shape once so the exact
        // field names show up in the log if this heuristic misses. Falls back
        // to the flat 0.5 the swap/resize features already use.
        private float RollTweakableValue(object tweakableElement, Random rng)
        {
            if (tweakableElement == null) return 0.5f;
            try
            {
                var t = tweakableElement.GetType();
                if (_dumpedTypeShapes.Add("TweakableValue-sample"))
                {
                    Log("One-time diagnostic: dumping a module's tweakable-value element shape (looking for the real Min/Max range to roll within).");
                    DumpValueShapeAndValues(tweakableElement, "tweakable value sample");
                }

                float? min = null, max = null;
                foreach (var p in t.GetProperties(BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Instance))
                {
                    if (p.GetIndexParameters().Length > 0) continue;
                    if (p.PropertyType != typeof(float) && p.PropertyType != typeof(double) && p.PropertyType != typeof(int)) continue;
                    string n = p.Name.ToLowerInvariant();
                    try
                    {
                        if (n.Contains("min")) min = Convert.ToSingle(p.GetValue(tweakableElement));
                        else if (n.Contains("max")) max = Convert.ToSingle(p.GetValue(tweakableElement));
                    }
                    catch { }
                }
                if (min.HasValue && max.HasValue && max.Value >= min.Value)
                    return (float)(min.Value + rng.NextDouble() * (max.Value - min.Value));
            }
            catch (Exception ex) { Log("RollTweakableValue: threw: " + ex.Message); }
            return 0.5f;
        }

        // Builds a full fresh module: real weighted rarity roll, real
        // Min/Max-rolled values where we could find them (else flat 0.5,
        // logged), level reset to 0 (a reroll is meant to be a brand new
        // draw, not a leveled-up version of the old one).
        private object BuildRerolledModule(Type moduleType, ModuleCandidate candidate, object rarityValue, Random rng)
        {
            if (moduleType == null || candidate == null) { Log("BuildRerolledModule: missing moduleType or candidate."); return null; }
            object newModule;
            try { newModule = Activator.CreateInstance(moduleType); }
            catch (Exception ex) { Log($"BuildRerolledModule: Activator.CreateInstance({moduleType.FullName}) threw: {ex.Message}"); return null; }

            if (!TrySetInstanceMemberValue(newModule, "m_ModuleGuid", candidate.Guid)) return null;
            TrySetInstanceMemberValue(newModule, "m_Rarity", rarityValue);
            TrySetInstanceMemberValue(newModule, "m_UpgradeLevel", 0);

            try
            {
                var getTweakables = candidate.Scriptable.GetType().GetMethod("GetTweakableValuesForRarity", BindingFlags.Public | BindingFlags.Instance);
                object list = getTweakables?.Invoke(candidate.Scriptable, new object[] { rarityValue });
                var countProp = list?.GetType().GetProperty("Count", BindingFlags.Public | BindingFlags.Instance);
                var listItemProp = list?.GetType().GetProperty("Item", BindingFlags.Public | BindingFlags.Instance);
                int rollCount = countProp != null ? Math.Max(1, (int)countProp.GetValue(list)) : 1;

                var rollsProp = moduleType.GetProperty("m_BaseValueRolls", BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Instance);
                if (rollsProp != null)
                {
                    var arrayType = rollsProp.PropertyType;
                    object newRolls = Activator.CreateInstance(arrayType, new object[] { rollCount });
                    var rollsItemProp = arrayType.GetProperty("Item", BindingFlags.Public | BindingFlags.Instance);
                    if (rollsItemProp != null)
                    {
                        for (int i = 0; i < rollCount; i++)
                        {
                            object tweakableElement = null;
                            if (listItemProp != null) { try { tweakableElement = listItemProp.GetValue(list, new object[] { i }); } catch { } }
                            rollsItemProp.SetValue(newRolls, RollTweakableValue(tweakableElement, rng), new object[] { i });
                        }
                    }
                    rollsProp.SetValue(newModule, newRolls);
                }
            }
            catch (Exception ex) { Log("BuildRerolledModule: rolls setup threw: " + ex.Message); }

            return newModule;
        }

        private void HandleRerollModule(HttpListenerContext ctx)
        {
            int bpIndex = QueryInt(ctx, "blueprintIndex", -1);
            int modIndex = QueryInt(ctx, "moduleIndex", -1);

            var blueprints = GetBlueprintsSnapshot();
            if (bpIndex < 0 || bpIndex >= blueprints.Count) { WriteJson(ctx, 400, "{\"error\":\"bad blueprintIndex\"}"); return; }
            object bp = blueprints[bpIndex];
            object generatedData = GetInstanceMemberValue(bp, "m_GeneratedData");
            object existingModule = GetModuleAt(generatedData, modIndex);
            if (existingModule == null) { WriteJson(ctx, 400, "{\"error\":\"bad moduleIndex\"}"); return; }
            Type moduleType = existingModule.GetType();

            if (_itemRarityType == null) _itemRarityType = FindType("Il2CppKeepsake.GeneratedItems.ItemRarity");
            object itemRarity = GetInstanceMemberValue(generatedData, "m_Rarity");
            string templateGuid = GetInstanceMemberValue(generatedData, "m_TemplateGuid") as string;
            if (_moduleCandidates.Count == 0) RefreshModuleCandidates(false);

            // What kind (basic/custom) is THIS slot right now? Read off the
            // module currently occupying it, not off its array index - index
            // alone doesn't reliably mean "Upgradeable Features" (confirmed:
            // Reactors have 1 basic slot, not the 2 most items have).
            string existingGuid = GetInstanceMemberValue(existingModule, "m_ModuleGuid") as string;
            var existingCandidate = FindCandidateByGuid(existingGuid);
            bool wantBasic = existingCandidate?.IsBasicModule ?? true;

            // Upgradeable Features don't have an independently-rollable
            // rarity in the real game - they always match the item's own
            // rarity. Rerolling one still picks a new module TYPE (that part
            // is legitimate - see the README on the module picker), but its
            // rarity must land back on the item's rarity, not a fresh
            // weighted roll like Custom Modules get.
            object rolledRarity = wantBasic ? itemRarity : RollModuleRarity(itemRarity, _rerollRng);
            string rolledRarityName = rolledRarity?.ToString();

            // Rarity-compatible AND allowed/forbidden-item-compatible with
            // this specific item template (e.g. don't reroll a ship weapon
            // into a module that's only meant for on-foot guns), AND
            // matches this slot's basic/custom kind (rerolling a fixed
            // "Upgradeable Features" slot must stay a basic module, and a
            // "Custom Modules" slot must stay non-basic, or the game will
            // show it under the wrong section). Each filter relaxes back to
            // the previous, wider pool if it comes up empty rather than
            // blocking reroll outright.
            var byRarity = new List<ModuleCandidate>();
            foreach (var c in _moduleCandidates)
                if (IsRarityWithinRange(c.Scriptable, rolledRarityName)) byRarity.Add(c);
            if (byRarity.Count == 0) byRarity.AddRange(_moduleCandidates);

            var byTemplate = new List<ModuleCandidate>();
            foreach (var c in byRarity)
                if (IsTemplateCompatible(c, templateGuid)) byTemplate.Add(c);
            if (byTemplate.Count == 0) byTemplate.AddRange(byRarity);

            var compatible = new List<ModuleCandidate>();
            foreach (var c in byTemplate)
                if (c.IsBasicModule == wantBasic) compatible.Add(c);
            if (compatible.Count == 0) compatible.AddRange(byTemplate);
            if (compatible.Count == 0) { WriteJson(ctx, 500, "{\"error\":\"no module candidates loaded - try Search Module DB first\"}"); return; }

            var picked = PickWeightedRandomCandidate(compatible, _rerollRng);
            if (picked == null) { WriteJson(ctx, 500, "{\"error\":\"weighted pick failed\"}"); return; }

            object newModule = BuildRerolledModule(moduleType, picked, rolledRarity, _rerollRng);
            if (newModule == null) { WriteJson(ctx, 500, "{\"error\":\"could not construct rerolled module\"}"); return; }

            bool wroteModuleBack = TryWriteModuleBack(generatedData, modIndex, newModule);
            bool wroteGeneratedBack = TrySetInstanceMemberValue(bp, "m_GeneratedData", generatedData);
            Log($"HandleRerollModule: blueprint[{bpIndex}] module[{modIndex}] rerolled to '{picked.DisplayName}' @ {rolledRarityName} (from {compatible.Count} compatible candidate(s)), wroteModuleBack={wroteModuleBack}, bp.m_GeneratedData wroteBack={wroteGeneratedBack}.");

            if (wroteModuleBack) SaveNow();
            WriteJson(ctx, 200, "{\"ok\":" + (wroteModuleBack ? "true" : "false") + ",\"name\":" + JsonStr(picked.DisplayName) + ",\"rarity\":" + JsonStr(rolledRarityName) + "}");
        }

        // Blueprint-side version of HandleSetInventoryModuleRoll - same
        // direct single-stat roll write, just against a blueprint's
        // m_GeneratedData instead of an inventory item's.
        private void HandleSetModuleRoll(HttpListenerContext ctx)
        {
            int bpIndex = QueryInt(ctx, "blueprintIndex", -1);
            int modIndex = QueryInt(ctx, "moduleIndex", -1);
            int tweakableIndex = QueryInt(ctx, "tweakableIndex", -1);
            float roll = QueryFloat(ctx, "roll", -1f);
            if (tweakableIndex < 0 || roll < 0f) { WriteJson(ctx, 400, "{\"error\":\"missing or bad tweakableIndex/roll\"}"); return; }

            var blueprints = GetBlueprintsSnapshot();
            if (bpIndex < 0 || bpIndex >= blueprints.Count) { WriteJson(ctx, 400, "{\"error\":\"bad blueprintIndex\"}"); return; }
            object bp = blueprints[bpIndex];
            object generatedData = GetInstanceMemberValue(bp, "m_GeneratedData");
            object module = GetModuleAt(generatedData, modIndex);
            if (module == null) { WriteJson(ctx, 400, "{\"error\":\"bad moduleIndex\"}"); return; }

            bool setOk = SetModuleRollValue(module, tweakableIndex, roll);
            bool wroteModuleBack = setOk && TryWriteModuleBack(generatedData, modIndex, module);
            bool wroteGeneratedBack = wroteModuleBack && TrySetInstanceMemberValue(bp, "m_GeneratedData", generatedData);
            Log($"HandleSetModuleRoll: blueprint[{bpIndex}] module[{modIndex}] tweakable[{tweakableIndex}] roll <- {roll}, wroteBack={wroteGeneratedBack}.");

            float currentValue = 0f;
            if (wroteGeneratedBack)
            {
                SaveNow();
                string mGuid = GetInstanceMemberValue(module, "m_ModuleGuid") as string;
                var candidate = FindCandidateByGuid(mGuid);
                if (candidate != null)
                {
                    object mRarity = GetInstanceMemberValue(module, "m_Rarity");
                    object mLevel = GetInstanceMemberValue(module, "m_UpgradeLevel");
                    currentValue = GetSingleTweakableCurrentValue(candidate.Scriptable, mRarity, mLevel, module, tweakableIndex);
                }
            }
            WriteJson(ctx, 200, "{\"ok\":" + (wroteGeneratedBack ? "true" : "false") + ",\"current\":" + currentValue.ToString(System.Globalization.CultureInfo.InvariantCulture) + "}");
        }

        // Forces an item's module count to match FixedUpgradeableModuleCount +
        // CustomModuleCountByRarity[current rarity] right now, without needing
        // to touch the rarity dropdown (ResizeModulesForRarity otherwise only
        // runs as a side effect of an actual rarity change).
        private void HandleNormalizeModuleCount(HttpListenerContext ctx)
        {
            int bpIndex = QueryInt(ctx, "blueprintIndex", -1);
            var blueprints = GetBlueprintsSnapshot();
            if (bpIndex < 0 || bpIndex >= blueprints.Count) { WriteJson(ctx, 400, "{\"error\":\"bad blueprintIndex\"}"); return; }
            object bp = blueprints[bpIndex];
            object generatedData = GetInstanceMemberValue(bp, "m_GeneratedData");

            int before = GetModuleCount(generatedData);
            object rarity = GetInstanceMemberValue(generatedData, "m_Rarity");
            string rarityName = rarity?.ToString();

            ResizeModulesForRarity(generatedData, rarityName, rarity, bp);
            bool wroteGeneratedBack = TrySetInstanceMemberValue(bp, "m_GeneratedData", generatedData);
            int after = GetModuleCount(generatedData);
            bool changed = before != after;
            Log($"HandleNormalizeModuleCount: blueprint[{bpIndex}] rarity='{rarityName}' module count {before} -> {after}, bp.m_GeneratedData wroteBack={wroteGeneratedBack}.");

            if (changed) SaveNow();
            WriteJson(ctx, 200, "{\"ok\":true,\"changed\":" + (changed ? "true" : "false") + ",\"before\":" + before + ",\"after\":" + after + "}");
        }

        // ---------- generic reflection helpers ----------

        private object GetPersistentUserData()
        {
            object mgr = GetStaticMemberValue(_mgrType, "Singleton");
            if (mgr == null) return null;
            object userDataReactive = GetInstanceMemberValue(mgr, "m_UserData");
            if (userDataReactive == null) return null;
            object userData = GetInstanceMemberValue(userDataReactive, "value");
            if (userData == null) userData = GetInstanceMemberValue(userDataReactive, "Value");
            return userData;
        }

        // Diagnoses "edits revert instantly, even before we save" reports:
        // reads m_UserData / GetPersistentUserData() / m_Blueprints TWICE in a
        // row with NO mutation at all in between, to find out at exactly which
        // layer a fresh object graph gets synthesized on every access (as
        // opposed to returning a stable reference), since that's what would
        // make any direct field write invisible to the very next read.
        private void DiagnoseUserDataStability()
        {
            object mgr = GetStaticMemberValue(_mgrType, "Singleton");
            if (mgr == null) { Log("DiagnoseUserDataStability: Singleton not found."); return; }

            object userDataReactive1 = GetInstanceMemberValue(mgr, "m_UserData");
            object userDataReactive2 = GetInstanceMemberValue(mgr, "m_UserData");
            Log($"DiagnoseUserDataStability: m_UserData field read twice -> same reactive-wrapper instance = {ReferenceEquals(userDataReactive1, userDataReactive2)}.");

            if (userDataReactive1 != null)
            {
                Log("DiagnoseUserDataStability: dumping shape of the m_UserData reactive wrapper itself (looking for how 'value'/'Value' is implemented - a plain field vs. a computed property matters a lot here):");
                DumpValueShapeAndValues(userDataReactive1, "m_UserData (reactive wrapper)");
            }

            object userData1 = GetPersistentUserData();
            object userData2 = GetPersistentUserData();
            Log($"DiagnoseUserDataStability: GetPersistentUserData() called twice, no mutation in between -> same PersistentUserData instance = {ReferenceEquals(userData1, userData2)}.");

            if (userData1 != null && userData2 != null)
            {
                object blueprints1 = GetInstanceMemberValue(userData1, "m_Blueprints");
                object blueprints2 = GetInstanceMemberValue(userData2, "m_Blueprints");
                Log($"DiagnoseUserDataStability: m_Blueprints read twice -> same List instance = {ReferenceEquals(blueprints1, blueprints2)}.");

                if (blueprints1 != null && blueprints2 != null)
                {
                    var list1 = ReadIndexedCollection(blueprints1);
                    var list2 = ReadIndexedCollection(blueprints2);
                    if (list1.Count > 0 && list2.Count > 0)
                    {
                        bool sameFirstBp = ReferenceEquals(list1[0], list2[0]);
                        Log($"DiagnoseUserDataStability: first Blueprint element read twice -> same object instance = {sameFirstBp}.");
                    }
                }
            }
        }

        // Investigates whether there's a separate list of loose/raw loot -
        // items picked up during a run but not yet turned into a Blueprint -
        // distinct from m_Blueprints. PersistentUserData is the exact same
        // save-data container m_Blueprints/m_BlueprintSlotCapacities already
        // live on (confirmed via DiagnoseUserDataStability above), so it's
        // the most likely home for an inventory list too. Dumps its full
        // shape (every field/prop, whatever it's actually called) plus a
        // type-based scan as a cross-check, same approach that found
        // GeneratedItem.m_Cosmetics when a name-based search came up empty.
        private void DumpInventoryDiscovery()
        {
            Log("========== INVENTORY DISCOVERY (looking for a loose-loot/inventory list separate from m_Blueprints) ==========");

            object userData = GetPersistentUserData();
            if (userData == null) { Log("DumpInventoryDiscovery: GetPersistentUserData() returned null - is a save loaded?"); return; }

            Log("---- full shape of PersistentUserData (same container m_Blueprints/m_BlueprintSlotCapacities live on) ----");
            DumpValueShapeAndValues(userData, "PersistentUserData");

            Log("---- scanning PersistentUserData for any member whose declared TYPE name contains inventory/loot/pickup/stash/cargo ----");
            var t = userData.GetType();
            var memberFlags = BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Instance;
            string[] keywords = { "inventory", "loot", "pickup", "stash", "cargo" };
            int hits = 0;
            try
            {
                foreach (var f in t.GetFields(memberFlags))
                {
                    string fullName = f.FieldType.FullName;
                    if (fullName == null) continue;
                    string lower = fullName.ToLowerInvariant();
                    if (!Array.Exists(keywords, k => lower.Contains(k))) continue;
                    hits++;
                    object val = SafeGet(() => f.GetValue(userData));
                    Log($"  [field] {fullName} {f.Name} = {DescribeValue(val)}");
                }
            }
            catch (Exception ex) { Log("DumpInventoryDiscovery: GetFields threw: " + ex.Message); }
            try
            {
                foreach (var p in t.GetProperties(memberFlags))
                {
                    if (p.GetIndexParameters().Length > 0) continue;
                    string fullName = p.PropertyType.FullName;
                    if (fullName == null) continue;
                    string lower = fullName.ToLowerInvariant();
                    if (!Array.Exists(keywords, k => lower.Contains(k))) continue;
                    hits++;
                    object val = SafeGet(() => p.GetValue(userData));
                    Log($"  [prop] {fullName} {p.Name} = {DescribeValue(val)}");
                }
            }
            catch (Exception ex) { Log("DumpInventoryDiscovery: GetProperties threw: " + ex.Message); }
            Log($"---- {hits} type-based inventory/loot-related member(s) found on PersistentUserData ----");

            // Round 2: m_Inventory is confirmed to exist as
            // List<Il2CppKeepsake.MetaProgression.InventoryItem> - dump its
            // live contents (or, if you're not currently carrying anything,
            // fall back to just dumping InventoryItem's member shape so we
            // still know the field names to build against).
            object inventoryList = GetInstanceMemberValue(userData, "m_Inventory");
            if (inventoryList == null)
            {
                Log("---- m_Inventory is null ----");
            }
            else
            {
                var items = ReadIndexedCollection(inventoryList);
                Log($"---- m_Inventory: {items.Count} item(s) - full shape for up to 5 samples ----");
                for (int i = 0; i < items.Count && i < 5; i++)
                    DumpValueShapeAndValues(items[i], $"m_Inventory[{i}]");
                if (items.Count == 0)
                {
                    Log("---- m_Inventory is empty right now - dumping InventoryItem's member shape directly instead (pick up some loot in-game and re-run this if you want live values) ----");
                    DumpTypeMembersByName("Il2CppKeepsake.MetaProgression.InventoryItem");
                }
            }

            Log("========== END INVENTORY DISCOVERY ==========");
        }

        // User asked whether inventory items could be replaced with
        // "artifacts" - the run-duration ship boosts you find and install
        // (has rarities, different boost effects like +shield). Earlier logs
        // from an unrelated scan already surfaced real evidence this is its
        // OWN system, not part of the 3-slot carried inventory: a dedicated
        // Artifact data class (PersistentArtifact property returning type
        // Artifact), a dedicated pickup pipeline (PickupableItem_Artifact
        // FirstPerson/ThirdPerson, ArtifactPersistentPickupable,
        // PickupableArtifactBlackboardData, VAssist_PickupableArtifact - 3
        // live "Pickupable_Artifact (Clone)" instances were seen sitting in
        // the world), and IsArtifact() sitting alongside IsConsumable()/
        // IsMeleeWeapon()/IsComponent() etc. as one of several "what kind of
        // pickupable is this" flags on the item-data class. That strongly
        // suggests Artifacts are a distinct "installed on the ship for the
        // run" system, not something that can just be dropped into an
        // InventoryItem's m_GUID like a consumable can. This looks for where
        // the PLAYER'S installed/owned Artifacts actually persist (mirroring
        // how m_Inventory/m_Blueprints were found on PersistentUserData) and
        // the shape of the Artifact class itself, before assuming anything
        // about whether/how this tool could edit them.
        private void DumpArtifactSystemDiscovery()
        {
            Log("========== ARTIFACT SYSTEM DISCOVERY ==========");

            object userData = GetPersistentUserData();
            if (userData == null) { Log("DumpArtifactSystemDiscovery: GetPersistentUserData() returned null - is a save loaded?"); Log("========== END ARTIFACT SYSTEM DISCOVERY =========="); return; }

            Log("---- scanning PersistentUserData for any member whose declared TYPE name contains 'artifact' ----");
            var t = userData.GetType();
            var memberFlags = BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Instance;
            int hits = 0;
            try
            {
                foreach (var f in t.GetFields(memberFlags))
                {
                    string fullName = f.FieldType.FullName;
                    if (fullName == null || fullName.IndexOf("artifact", StringComparison.OrdinalIgnoreCase) < 0) continue;
                    hits++;
                    object val = SafeGet(() => f.GetValue(userData));
                    Log($"  [field] {fullName} {f.Name} = {DescribeValue(val)}");
                }
            }
            catch (Exception ex) { Log("DumpArtifactSystemDiscovery: GetFields threw: " + ex.Message); }
            try
            {
                foreach (var p in t.GetProperties(memberFlags))
                {
                    if (p.GetIndexParameters().Length > 0) continue;
                    string fullName = p.PropertyType.FullName;
                    if (fullName == null || fullName.IndexOf("artifact", StringComparison.OrdinalIgnoreCase) < 0) continue;
                    hits++;
                    object val = SafeGet(() => p.GetValue(userData));
                    Log($"  [prop] {fullName} {p.Name} = {DescribeValue(val)}");
                }
            }
            catch (Exception ex) { Log("DumpArtifactSystemDiscovery: GetProperties threw: " + ex.Message); }
            Log($"---- {hits} artifact-related member(s) found directly on PersistentUserData ----");

            Log("---- scanning all loaded assemblies for type names that are exactly 'Artifact', or contain 'Artifact' alongside Manager/Catalog/Library/Save/Persistent/Collection/Data ----");
            Type coreArtifactType = null;
            var candidateContainerTypes = new List<Type>();
            foreach (var asm in AppDomain.CurrentDomain.GetAssemblies())
            {
                Type[] types;
                try { types = asm.GetTypes(); }
                catch (ReflectionTypeLoadException rtle)
                {
                    var loaded = new List<Type>();
                    foreach (var rt in rtle.Types) if (rt != null) loaded.Add(rt);
                    types = loaded.ToArray();
                }
                catch { continue; }

                foreach (var ty in types)
                {
                    if (ty == null) continue;
                    if (ty.Name == "Artifact") { coreArtifactType = ty; Log($"  core type: {ty.FullName}"); continue; }
                    if (ty.Name.IndexOf("Artifact", StringComparison.OrdinalIgnoreCase) < 0) continue;
                    string[] containerHints = { "Manager", "Catalog", "Library", "Save", "Persistent", "Collection", "Data" };
                    foreach (var hint in containerHints)
                    {
                        if (ty.Name.IndexOf(hint, StringComparison.OrdinalIgnoreCase) >= 0)
                        {
                            candidateContainerTypes.Add(ty);
                            break;
                        }
                    }
                }
            }

            if (coreArtifactType != null)
            {
                Log("---- full member dump: core Artifact type ----");
                DumpTypeMembersByName(coreArtifactType.FullName);
            }
            else
            {
                Log("  No type named exactly 'Artifact' found.");
            }

            Log($"---- {candidateContainerTypes.Count} candidate container/manager/catalog type(s) with 'Artifact' + a Manager/Catalog/Library/Save/Persistent/Collection/Data hint in the name ----");
            foreach (var ty in candidateContainerTypes) Log($"  {ty.FullName}");
            foreach (var ty in candidateContainerTypes)
            {
                Log($"---- full member dump: {ty.FullName} ----");
                DumpTypeMembersByName(ty.FullName);
            }

            // Round 2 (candidateContainerTypes above turned out to be a dead
            // end on a real run - all 3 were world-pickup/HUD-icon types, not
            // a save container). Two follow-ups: (a) the Manager/Catalog/
            // etc. hint filter may have been too narrow - list every
            // "Artifact"-named type with no filter at all so nothing's hidden
            // by a guessed keyword; (b) "install onto your ship for the
            // duration of the run" (the user's own description) suggests
            // this might not be a flat PersistentUserData field at all - it
            // could be nested inside a per-ship or per-venture structure
            // instead (m_OwnedShips/m_ActiveVentures), or it might not
            // persist across saves at all (run-scoped only), which would
            // explain 0 hits on PersistentUserData directly. Dumps the full
            // shape of the most likely nesting spots so that's visible
            // either way.
            Log("---- unfiltered: every type anywhere in loaded assemblies with 'Artifact' in the name (no Manager/Catalog/etc. filter this time) ----");
            var allArtifactTypeNames = new List<string>();
            foreach (var asm in AppDomain.CurrentDomain.GetAssemblies())
            {
                Type[] types;
                try { types = asm.GetTypes(); }
                catch (ReflectionTypeLoadException rtle)
                {
                    var loaded = new List<Type>();
                    foreach (var rt in rtle.Types) if (rt != null) loaded.Add(rt);
                    types = loaded.ToArray();
                }
                catch { continue; }
                foreach (var ty in types)
                {
                    if (ty == null || ty.Name.IndexOf("Artifact", StringComparison.OrdinalIgnoreCase) < 0) continue;
                    allArtifactTypeNames.Add(ty.FullName);
                }
            }
            foreach (var n in allArtifactTypeNames) Log($"  {n}");
            Log($"---- {allArtifactTypeNames.Count} total 'Artifact'-named type(s) ----");

            Log("---- checking likely nesting spots on PersistentUserData for an installed-artifacts list one level deeper (m_LootProgression, m_PlayerProgression, m_OwnedShips[0], m_ActiveVentures[0]) ----");
            object lootProgression = GetInstanceMemberValue(userData, "m_LootProgression");
            if (lootProgression != null) DumpValueShapeAndValues(lootProgression, "m_LootProgression");
            else Log("  m_LootProgression is null.");

            object playerProgression = GetInstanceMemberValue(userData, "m_PlayerProgression");
            if (playerProgression != null) DumpValueShapeAndValues(playerProgression, "m_PlayerProgression");
            else Log("  m_PlayerProgression is null.");

            object ownedShips = GetInstanceMemberValue(userData, "m_OwnedShips");
            if (ownedShips != null)
            {
                List<object> shipEntries;
                try { shipEntries = ReadIndexedCollection(ownedShips); }
                catch (Exception ex) { shipEntries = new List<object>(); Log("  m_OwnedShips could not be read as a collection: " + ex.Message); }
                Log($"  m_OwnedShips: {shipEntries.Count} entr(y/ies).");
                if (shipEntries.Count > 0) DumpValueShapeAndValues(shipEntries[0], "m_OwnedShips[0]");
            }
            else Log("  m_OwnedShips is null.");

            object activeVentures = GetInstanceMemberValue(userData, "m_ActiveVentures");
            if (activeVentures != null)
            {
                List<object> ventureEntries;
                try { ventureEntries = ReadIndexedCollection(activeVentures); }
                catch (Exception ex) { ventureEntries = new List<object>(); Log("  m_ActiveVentures could not be read as a collection: " + ex.Message); }
                Log($"  m_ActiveVentures: {ventureEntries.Count} entr(y/ies).");
                if (ventureEntries.Count > 0) DumpValueShapeAndValues(ventureEntries[0], "m_ActiveVentures[0]");
            }
            else Log("  m_ActiveVentures is null.");

            // Round 3 (m_LootProgression/m_PlayerProgression/m_OwnedShips[0]/
            // m_ActiveVentures[0] from round 2 all confirmed - real run,
            // dumped above - to have NO Artifact-typed field anywhere in
            // their shape, so installed Artifacts are not nested under any
            // of those 4 spots either. Two things left to try: (a) full
            // member dump of the most promising leads from the round-2
            // unfiltered type list - HostResumeArtifact/
            // HostResumeArtifactCabinet (same MetaProgression namespace as
            // the confirmed save types, each with its own MessagePack
            // Formatter, meaning these ARE serializable - "HostResume"
            // suggests they back the co-op mid-mission resume snapshot,
            // which would explain why they're not reachable from the
            // hangar's PersistentUserData at all) and ArtifactCabinet/
            // VAssist_ArtifactCabinet ("Cabinet" reads as the actual
            // ship-side slotted storage for installed Artifacts); (b) in
            // case ArtifactCabinet is a live scene component rather than
            // save data (same shape as the PlayerPickupableItemHandler
            // hotbar case), try to find a live instance of it the same way
            // - this will only find anything while actually in a mission
            // with the ship loaded, so an empty result here is expected
            // while sitting in the hangar and is not itself conclusive.
            Log("---- round 3: full member dump of the most promising leads from the unfiltered list above ----");
            string[] leadTypeNames =
            {
                "Il2CppKeepsake.MetaProgression.HostResumeArtifact",
                "Il2CppKeepsake.MetaProgression.HostResumeArtifactCabinet",
                "Il2CppKeepsake.ArtifactCabinet",
                "Il2CppKeepsake.VAssist_ArtifactCabinet",
            };
            foreach (var leadName in leadTypeNames)
            {
                Log($"---- full member dump: {leadName} ----");
                DumpTypeMembersByName(leadName);
            }

            Log("---- round 3: checking for a LIVE scene instance of ArtifactCabinet / VAssist_ArtifactCabinet (only expected to find anything while actually in a mission, not in the hangar) ----");
            string[] liveCandidateNames = { "Il2CppKeepsake.ArtifactCabinet", "Il2CppKeepsake.VAssist_ArtifactCabinet" };
            foreach (var liveName in liveCandidateNames)
            {
                Type liveType = FindType(liveName);
                if (liveType == null) { Log($"  {liveName}: type not found."); continue; }
                object found = TryFindAllObjectsOfType(liveType);
                List<object> instances;
                try { instances = found != null ? ReadIndexedCollection(found) : new List<object>(); }
                catch (Exception ex) { instances = new List<object>(); Log($"  {liveName}: could not read FindObjectsOfType result as a collection: {ex.Message}"); }
                Log($"  {liveName}: {instances.Count} live instance(s) found.");
                for (int i = 0; i < instances.Count; i++)
                {
                    object inst = TryCastToType(instances[i], liveType);
                    DumpValueShapeAndValues(inst, $"{liveName}[{i}]");
                }
            }

            Log("Send this log along - looking for whichever field/property actually holds the player's currently-installed Artifacts (mirrors how m_Inventory holds carried items), plus Artifact's own fields (rarity, boost type/guid) to see if a catalog swap like the consumable one could work here too. If the round-3 leads above also come up empty, please run this diagnostic again WHILE OUT ON A MISSION with at least one Artifact actually installed on the ship - installed Artifacts increasingly look like genuinely run-scoped state (possibly tied to the co-op host-resume snapshot) that simply doesn't exist at all while sitting in the hangar with no active venture.");
            Log("========== END ARTIFACT SYSTEM DISCOVERY ==========");
        }

        // Looking for whatever determines the order blueprints show up in on
        // the real assembler screen, so the web UI's per-category list can
        // match it instead of whatever order m_Blueprints itself happens to
        // return them in (which may just be creation/acquisition order, not
        // display order). Three angles at once: (1) print m_Blueprints' own
        // order alongside name/rarity/level so it can be eyeballed against
        // what you see in-game, (2) full shape of blueprints[0] looking for
        // any timestamp/sort-index-looking field we haven't exposed yet, (3)
        // m_BlueprintHistory - a separate list PersistentUserData carries
        // that might record acquisition order even if m_Blueprints doesn't.
        private void DumpBlueprintOrderingDiscovery()
        {
            Log("========== BLUEPRINT ORDERING DISCOVERY ==========");

            var blueprints = GetBlueprintsSnapshot();
            Log($"---- m_Blueprints as returned by the list - {blueprints.Count} entr(y/ies), in this order ----");
            for (int i = 0; i < blueprints.Count; i++)
            {
                object bp = blueprints[i];
                object generatedData = GetInstanceMemberValue(bp, "m_GeneratedData");
                string name = AsString(GetInstanceMemberValue(generatedData, "ResolvedName"));
                object rarity = GetInstanceMemberValue(generatedData, "m_Rarity");
                object level = GetInstanceMemberValue(generatedData, "m_Level");
                string guid = GetInstanceMemberValue(bp, "m_Guid") as string;
                string categoryGuid = GetInstanceMemberValue(bp, "m_CategoryGuid") as string;
                Log($"  [{i}] \"{name}\" rarity={rarity} level={level} categoryGuid={categoryGuid} guid={guid}");
            }

            if (blueprints.Count > 0)
            {
                Log("---- full shape of blueprints[0] (looking for a timestamp/sort-index field beyond what's already exposed above) ----");
                DumpValueShapeAndValues(blueprints[0], "blueprints[0]");
            }

            object userData = GetPersistentUserData();
            if (userData == null) { Log("DumpBlueprintOrderingDiscovery: GetPersistentUserData() returned null - is a save loaded?"); Log("========== END BLUEPRINT ORDERING DISCOVERY =========="); return; }

            object history = null;
            try { history = GetInstanceMemberValue(userData, "m_BlueprintHistory"); }
            catch (Exception ex) { Log("DumpBlueprintOrderingDiscovery: reading m_BlueprintHistory threw: " + ex.Message); }

            if (history == null)
            {
                Log("---- m_BlueprintHistory is null ----");
            }
            else
            {
                var histItems = ReadIndexedCollection(history);
                Log($"---- m_BlueprintHistory: {histItems.Count} entr(y/ies) - full shape for up to 5 samples ----");
                for (int i = 0; i < histItems.Count && i < 5; i++)
                    DumpValueShapeAndValues(histItems[i], $"m_BlueprintHistory[{i}]");
            }

            // Blueprints already carry a real m_SlotIndex (confirmed - it's
            // been read and shown in the UI as "slot N" this whole time), and
            // per your description the game clearly treats it as a genuine,
            // sparse, player-arranged position (slots 1-5 empty, slot 6
            // filled is a real case) rather than an auto-assigned dense
            // counter - so sorting by it is the right fix for display order,
            // already done client-side. What's still missing to also render
            // the EMPTY slots themselves (not just gaps between two owned
            // items) is each category's total unlocked slot count. We've
            // only ever read m_CategoryGuid off m_BlueprintSlotCapacities
            // entries before - dumping the full shape of one here to find
            // whatever field holds the actual capacity number.
            var caps = GetBlueprintSlotCapacities();
            Log($"---- m_BlueprintSlotCapacities: {caps.Count} entr(y/ies) - full shape of entry[0] (looking for the capacity/count field) ----");
            if (caps.Count > 0) DumpValueShapeAndValues(caps[0], "m_BlueprintSlotCapacities[0]");
            Log("---- every m_BlueprintSlotCapacities entry's categoryGuid (cross-check against CategoryByGuid) ----");
            for (int i = 0; i < caps.Count; i++)
            {
                string guid = GetInstanceMemberValue(caps[i], "m_CategoryGuid") as string;
                Log($"  [{i}] categoryGuid={guid}");
            }

            Log("========== END BLUEPRINT ORDERING DISCOVERY ==========");
            Log("If none of the above has an obvious order/timestamp field: open the assembler in-game, note the exact order items appear in ONE category (e.g. Weapons), and send that alongside this log - matching it against the [i] index/guid list above may reveal a sort rule (by name, by level, by rarity, etc.) even with no persisted order field.");
        }

        // Reads a List<T>/IReadOnlyList<T>/array-shaped value generically.
        // IL2CPP interop collections are inconsistent about what reflection can
        // actually see on them, so this tries several strategies in order,
        // falling through to the next only if the previous one comes up empty:
        //   1. Count/Item property (lists) - checking base interfaces too, since
        //      Type.GetProperty on an interface does NOT search base interfaces
        //      by default (Count lives on IReadOnlyCollection<T>, a base of
        //      IReadOnlyList<T>) and a plain GetProperty("Count") silently
        //      returns null.
        //   2. Length/Item property (arrays - Il2CppReferenceArray<T> etc. use
        //      "Length", not "Count").
        //   3. get_Count/get_Length + get_Item as raw MethodInfo instead of
        //      PropertyInfo, in case the interop-generated metadata links the
        //      accessor methods but not the property wrapper itself.
        //   4. Manual GetEnumerator/MoveNext/Current walk, for the rare case
        //      where even an indexer isn't reachable but enumeration is.
        // Logs a "here's how this collection type reads" line only the first
        // time it's seen for a given (strategy, type) pair - reused HashSet
        // from the one-time type-shape dumps elsewhere in this file. Needed
        // because ReadIndexedCollection now gets called every few seconds by
        // the gameState poll, and re-logging the same successful read forever
        // was drowning out everything else in Editor_Log.txt.
        private void LogCollectionReadOnce(Type t, string strategyKey, string message)
        {
            if (_dumpedTypeShapes.Add("ReadIndexedCollection-" + strategyKey + "-" + t.FullName)) Log(message);
        }

        private List<object> ReadIndexedCollection(object collection)
        {
            var result = new List<object>();
            if (collection == null) return result;
            var t = collection.GetType();

            foreach (var countName in new[] { "Count", "Length" })
            {
                var countProp = FindPropertyIncludingInterfaces(t, countName);
                var itemProp = FindPropertyIncludingInterfaces(t, "Item");
                if (countProp == null || itemProp == null) continue;
                try
                {
                    int count = (int)countProp.GetValue(collection);
                    // Logged once per collection type, not every call - this
                    // gets hit every few seconds now (gameState polling reads
                    // the blueprint list repeatedly), and once we've confirmed
                    // a type reads fine there's nothing new to learn from
                    // seeing the same line forever.
                    LogCollectionReadOnce(t, "count-item", $"{t.FullName}: read via {countName}/Item property - {countName}={count}.");
                    for (int i = 0; i < count; i++)
                    {
                        object item = itemProp.GetValue(collection, new object[] { i });
                        if (item != null) result.Add(item);
                    }
                    return result;
                }
                catch (Exception ex) { Log($"{t.FullName}: {countName}/Item property read failed: {ex.Message}"); }
            }

            foreach (var countName in new[] { "get_Count", "get_Length" })
            {
                var countMethod = FindMethodIncludingInterfaces(t, countName, 0);
                var itemMethod = FindMethodIncludingInterfaces(t, "get_Item", 1);
                if (countMethod == null || itemMethod == null) continue;
                try
                {
                    int count = (int)countMethod.Invoke(collection, null);
                    LogCollectionReadOnce(t, "count-getitem", $"{t.FullName}: read via {countName}/get_Item method - {countName}={count}.");
                    for (int i = 0; i < count; i++)
                    {
                        object item = itemMethod.Invoke(collection, new object[] { i });
                        if (item != null) result.Add(item);
                    }
                    return result;
                }
                catch (Exception ex) { Log($"{t.FullName}: {countName}/get_Item method invoke failed: {ex.Message}"); }
            }

            var getEnum = FindMethodIncludingInterfaces(t, "GetEnumerator", 0);
            if (getEnum != null)
            {
                try
                {
                    object enumerator = getEnum.Invoke(collection, null);
                    if (enumerator != null)
                    {
                        var enumType = enumerator.GetType();
                        var moveNext = FindMethodIncludingInterfaces(enumType, "MoveNext", 0);
                        var currentProp = FindPropertyIncludingInterfaces(enumType, "Current");
                        if (moveNext != null && currentProp != null)
                        {
                            while ((bool)moveNext.Invoke(enumerator, null))
                            {
                                object item = currentProp.GetValue(enumerator);
                                if (item != null) result.Add(item);
                            }
                            LogCollectionReadOnce(t, "enumerator", $"{t.FullName}: read via GetEnumerator - found {result.Count} item(s).");
                            return result;
                        }
                    }
                }
                catch (Exception ex) { Log($"{t.FullName}: GetEnumerator fallback failed: {ex.Message}"); }
            }

            // Confirmed via type-shape dump: some IL2CPP interface-projection
            // wrappers (e.g. IngotCurrencies's IReadOnlyList<Currency>) only
            // implement a bare indexer (Item/get_Item) with NO Count, Length,
            // or GetEnumerator at all - the interop generator only stubs out
            // interface members the game's own compiled code actually calls,
            // and nothing here calls .Count. Without a count, walk indices
            // upward and stop at the first one that throws or comes back null
            // (native out-of-range), same as reading a native array blind.
            var bareItemProp = FindPropertyIncludingInterfaces(t, "Item");
            var bareItemMethod = bareItemProp == null ? FindMethodIncludingInterfaces(t, "get_Item", 1) : null;
            if (bareItemProp != null || bareItemMethod != null)
            {
                const int hardCap = 500; // safety limit in case an indexer never throws
                for (int i = 0; i < hardCap; i++)
                {
                    object item;
                    try
                    {
                        item = bareItemProp != null
                            ? bareItemProp.GetValue(collection, new object[] { i })
                            : bareItemMethod.Invoke(collection, new object[] { i });
                    }
                    catch { break; }
                    if (item == null) break;
                    result.Add(item);
                }
                if (result.Count > 0)
                {
                    LogCollectionReadOnce(t, "bare-indexer", $"{t.FullName}: no Count/Length exposed - read {result.Count} items by probing the bare indexer until it stopped.");
                    return result;
                }
            }

            Log($"{t.FullName} could not be read via Count/Item, Length/Item, get_Count/get_Item methods, GetEnumerator, or bare-indexer probing.");
            DumpTypeShape(t);
            return result;
        }

        // One-shot diagnostic: when every read strategy above fails, print
        // everything reflection can actually see on the type - every field,
        // property, and method (public + nonpublic), plus its base type and
        // every interface it implements - so we can see exactly what's really
        // there instead of guessing another strategy blind.
        private readonly HashSet<string> _dumpedTypeShapes = new HashSet<string>();
        private void DumpTypeShape(Type t)
        {
            string key = t.FullName ?? t.Name;
            if (!_dumpedTypeShapes.Add(key)) return; // only dump each distinct type once per session

            var flags = BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Instance | BindingFlags.Static;
            Log($"--- type shape dump for {key} ---");
            Log($"  BaseType: {(t.BaseType == null ? "(none)" : t.BaseType.FullName)}");

            var ifaceNames = new List<string>();
            foreach (var iface in t.GetInterfaces()) ifaceNames.Add(iface.FullName);
            Log($"  Interfaces ({ifaceNames.Count}): {string.Join(", ", ifaceNames)}");

            try
            {
                var fields = t.GetFields(flags);
                Log($"  Fields ({fields.Length}):");
                foreach (var f in fields) Log($"    {f.FieldType.Name} {f.Name}");
            }
            catch (Exception ex) { Log("  GetFields threw: " + ex.Message); }

            try
            {
                var props = t.GetProperties(flags);
                Log($"  Properties ({props.Length}):");
                foreach (var p in props) Log($"    {p.PropertyType.Name} {p.Name}");
            }
            catch (Exception ex) { Log("  GetProperties threw: " + ex.Message); }

            try
            {
                var methods = t.GetMethods(flags);
                Log($"  Methods ({methods.Length}):");
                foreach (var m in methods) Log($"    {m.ReturnType.Name} {m.Name}({m.GetParameters().Length} params)");
            }
            catch (Exception ex) { Log("  GetMethods threw: " + ex.Message); }

            Log($"--- end type shape dump for {key} ---");
        }

        // Deliberately does NOT call the Type.GetProperty(name, flags) overload.
        // That overload throws AmbiguousMatchException whenever two properties
        // share a name in the hierarchy - which happens here: Il2CppArrayBase<T>
        // redeclares "Length" with the "new" keyword to hide Il2CppArrayBase's
        // own Length, so GetProperty("Length") on any Il2CppReferenceArray<T> /
        // Il2CppStructArray<T> throws instead of just returning the derived one.
        // Enumerating GetProperties() and filtering by name ourselves sidesteps
        // that entirely (GetProperties() never throws for this).
        private static PropertyInfo FindPropertyIncludingInterfaces(Type t, string name)
        {
            var flags = BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Instance;
            try
            {
                foreach (var p in t.GetProperties(flags))
                    if (p.Name == name) return p;
            }
            catch { }
            foreach (var iface in t.GetInterfaces())
            {
                try
                {
                    foreach (var p in iface.GetProperties(flags))
                        if (p.Name == name) return p;
                }
                catch { }
            }
            return null;
        }

        // Same defensive shape as FindPropertyIncludingInterfaces, and for the
        // same reason: t.GetMethods(flags) can throw for some closed generic
        // IL2CPP interop types (confirmed: it silently killed the WHOLE
        // ReadIndexedCollection call for Il2CppReferenceArray<UnityEngine.Object>
        // specifically, since this used to be called with no try/catch around
        // it - the exception propagated all the way out to the HTTP dispatcher,
        // which just sent a 500 and never reached any of our own Log() calls,
        // which is why no diagnostic line showed up for that failure at all).
        private static MethodInfo FindMethodIncludingInterfaces(Type t, string name, int paramCount)
        {
            var flags = BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Instance;
            try
            {
                foreach (var m in t.GetMethods(flags))
                    if (m.Name == name && m.GetParameters().Length == paramCount) return m;
            }
            catch { }
            foreach (var iface in t.GetInterfaces())
            {
                try
                {
                    foreach (var m in iface.GetMethods(flags))
                        if (m.Name == name && m.GetParameters().Length == paramCount) return m;
                }
                catch { }
            }
            return null;
        }

        // Loose carried items - confirmed via "Inspect Inventory Discovery" to
        // be a real, separate List<InventoryItem> from m_Blueprints, each with
        // m_GUID, m_ResourceAmount (Single), m_GeneratedData (the SAME
        // GeneratedItem type blueprints use - full rarity/level/modules/
        // cosmetics/template access via the exact same helpers), and
        // m_AmmoInMag (Int32, currently-loaded ammo if this happens to be a
        // weapon). Unlike blueprints there's no m_SlotIndex/m_CategoryGuid -
        // these are just "whatever you're currently carrying", not sorted
        // into the assembler's category/slot system at all.
        private List<object> GetInventorySnapshot()
        {
            try
            {
                object list = GetInventoryListRaw();
                return ReadIndexedCollection(list);
            }
            catch (Exception ex)
            {
                Log("Error reading inventory: " + ex.Message);
                return new List<object>();
            }
        }

        private object GetInventoryListRaw()
        {
            object userData = GetPersistentUserData();
            if (userData == null) return null;
            return GetInstanceMemberValue(userData, "m_Inventory");
        }

        // Generic version of TryWriteModuleBack for a List<T> rather than an
        // Il2CppReferenceArray<T> - same "boxed copy needs writing back into
        // its real container via the Item indexer setter" concern applies to
        // InventoryItem itself (isWrapped=False, same as Blueprint), not just
        // to GeneratedItem/GeneratedModule inside it.
        private bool TryWriteListItemBack(object list, int index, object mutatedItem)
        {
            if (list == null) { Log("TryWriteListItemBack: list is null."); return false; }
            var itemProp = list.GetType().GetProperty("Item", BindingFlags.Public | BindingFlags.Instance);
            if (itemProp == null) { Log("TryWriteListItemBack: list has no Item property."); return false; }
            if (!itemProp.CanWrite) { Log("TryWriteListItemBack: list.Item has no setter (CanWrite=false) - type " + list.GetType().FullName + "."); return false; }
            try { itemProp.SetValue(list, mutatedItem, new object[] { index }); return true; }
            catch (Exception ex) { Log($"TryWriteListItemBack: set_Item({index}) threw: {ex.Message}"); return false; }
        }

        // PersistentUserData.m_Inventory (what TryWriteListItemBack mutates
        // above, and what actually gets written to disk via SaveDataToCloud)
        // turned out to be a completely separate object from
        // MetaProgressionManager's OWN live m_Inventory/PersistentInventory
        // ReactiveCollection - the thing the game's actual gameplay/HUD code
        // observes. User feedback confirmed this: a consumable swap wrote
        // correctly (confirmed via Deep Dump immediately after) and
        // presumably saved fine, but never showed up in-game even across a
        // GUI refresh, and this game has no inventory-open menu event that
        // might otherwise force a resync. A live method dump of
        // MetaProgressionManager found the missing piece:
        // SetPlayerPersistentInventory(List<InventoryItem>), public and
        // static - the official way to push a full inventory list into the
        // manager's own live state. Same "call the game's own method rather
        // than hand-roll the propagation" idea as TryUpgradeBlueprint for
        // blueprints. Called after every inventory write below.
        // Logs a one-line summary of whatever the manager's own live
        // inventory collection currently looks like (count + each item's
        // guid), so a before/after pair around the SetPlayerPersistentInventory
        // call can show directly whether that call actually changed the
        // manager's own state - not just whether it ran without throwing.
        private string SummarizeManagerLiveInventory()
        {
            try
            {
                object mgr = GetStaticMemberValue(_mgrType, "Singleton");
                if (mgr == null) return "(no Singleton)";
                object liveInv = SafeGet(() => GetInstanceMemberValue(mgr, "m_Inventory"))
                                  ?? SafeGet(() => GetInstanceMemberValue(mgr, "PersistentInventory"));
                if (liveInv == null) return "(manager has no readable m_Inventory/PersistentInventory)";
                var items = ReadIndexedCollection(liveInv);
                var guids = new List<string>();
                foreach (var it in items) guids.Add(GetInstanceMemberValue(it, "m_GUID") as string ?? "?");
                return $"count={items.Count} guids=[{string.Join(", ", guids)}]";
            }
            catch (Exception ex) { return "(threw: " + ex.Message + ")"; }
        }

        private void PushInventoryLive(object mutatedList)
        {
            if (mutatedList == null) return;
            Log("PushInventoryLive: manager live inventory BEFORE = " + SummarizeManagerLiveInventory());
            try
            {
                var setInvMethod = _mgrType?.GetMethod("SetPlayerPersistentInventory", BindingFlags.Public | BindingFlags.Static);
                if (setInvMethod == null) { Log("PushInventoryLive: SetPlayerPersistentInventory method not found - in-game display may not refresh live (save data is still correct)."); return; }
                setInvMethod.Invoke(null, new object[] { mutatedList });
                Log("PushInventoryLive: SetPlayerPersistentInventory invoked without throwing.");
            }
            catch (Exception ex) { Log("PushInventoryLive: SetPlayerPersistentInventory threw: " + ex.Message); }
            Log("PushInventoryLive: manager live inventory AFTER = " + SummarizeManagerLiveInventory());
        }

        // Wraps TryWriteListItemBack + PushInventoryLive together so every
        // inventory write handler gets the live-refresh push automatically
        // just by switching to this instead of the raw
        // TryWriteListItemBack(GetInventoryListRaw(), ...) call.
        private bool TryWriteInventoryItemBack(int index, object mutatedItem)
        {
            object list = GetInventoryListRaw();
            bool wrote = TryWriteListItemBack(list, index, mutatedItem);
            if (wrote) PushInventoryLive(list);
            return wrote;
        }

        private static string InvSnapshotKey(int index) => "inv:" + index;

        private List<object> GetBlueprintsSnapshot()
        {
            try
            {
                object userData = GetPersistentUserData();
                if (userData == null) return new List<object>();
                object blueprintsList = GetInstanceMemberValue(userData, "m_Blueprints");
                return ReadIndexedCollection(blueprintsList);
            }
            catch (Exception ex)
            {
                Log("Error reading blueprints: " + ex.Message);
                return new List<object>();
            }
        }

        private List<object> GetBlueprintSlotCapacities()
        {
            try
            {
                object userData = GetPersistentUserData();
                if (userData == null) return new List<object>();
                object capsList = GetInstanceMemberValue(userData, "m_BlueprintSlotCapacities");
                return ReadIndexedCollection(capsList);
            }
            catch (Exception ex)
            {
                Log("Error reading BlueprintSlotCapacities: " + ex.Message);
                return new List<object>();
            }
        }

        // Confirmed via a real log: BlueprintSlotCapacity has m_CategoryGuid
        // (already used elsewhere) + m_MaxSlots (Int32) - the total number of
        // unlocked slots for that category, e.g. Weapons=6. Combined with each
        // blueprint's own m_SlotIndex (also confirmed real and sparse - slots
        // 1-5 empty with only slot 6 filled is a genuine, player-arranged
        // case), this is everything needed to render every EMPTY slot in a
        // category, not just gaps between two owned items.
        private string BuildBlueprintSlotCapacitiesJson()
        {
            var caps = GetBlueprintSlotCapacities();
            var categoryMap = GetCategoryMap();
            var sb = new StringBuilder();
            sb.Append("[");
            for (int i = 0; i < caps.Count; i++)
            {
                if (i > 0) sb.Append(",");
                string guid = GetInstanceMemberValue(caps[i], "m_CategoryGuid") as string;
                int maxSlots = SafeInt(GetInstanceMemberValue(caps[i], "m_MaxSlots"));
                string group = null, category = null;
                if (guid != null && categoryMap.TryGetValue(guid, out var info)) { group = info.group; category = info.name; }
                sb.Append("{\"categoryGuid\":").Append(JsonStr(guid))
                  .Append(",\"group\":").Append(JsonStr(group))
                  .Append(",\"category\":").Append(JsonStr(category))
                  .Append(",\"maxSlots\":").Append(maxSlots)
                  .Append("}");
            }
            sb.Append("]");
            return sb.ToString();
        }

        // Verified directly from Editor_Log categories.txt (a real dump of your
        // 38 owned blueprints): every guid below was cross-checked two ways -
        // once via m_BlueprintSlotCapacities and once by grouping your actual
        // items by their shared m_CategoryGuid (e.g. Lance Railgun and
        // Thunderburst Heavy Cannon both came back under
        // 9eb5cd7261a6dba439db975e7e05d069, matching what you'd already told me
        // is Special Weapons). Turns out the old positional guess had 8 of 9
        // slots wrong - only "Weapons" happened to land in the right spot.
        // Hardcoded by guid (not position), so this can't drift even if the
        // game ever returns m_BlueprintSlotCapacities in a different order.
        private static readonly Dictionary<string, (string group, string name)> CategoryByGuid =
            new Dictionary<string, (string, string)>(StringComparer.OrdinalIgnoreCase)
            {
                { "fd51532d25c4d4841b1c439708726682", ("Equipment", "Weapons") },
                { "d7c2724a0c49930438f6d6ed3da628ba", ("Components", "Engines") },
                { "2546892240b110847b64e524e9bd1d39", ("Components", "Reactors") },
                { "6ef31e2e90989364d8e2d4958615b299", ("Components", "Sensors") },
                { "9eb5cd7261a6dba439db975e7e05d069", ("Components", "Special Weapons") },
                { "00ef3c858516b02498fcf9e8ee5497de", ("Components", "Pilot Cannons") },
                { "0c28f786865a0b142926742a182c0011", ("Components", "Aux. Generators") },
                { "110603b5e382aec438ef983ddde55f81", ("Components", "Multiturrets") },
                { "1292627bbf531c84ba2c56e6e55af6d3", ("Components", "Shield Generators") },
            };

        // User-confirmed name overrides - kept as a belt-and-suspenders backup
        // in case a guid ever comes back missing/different for one of these.
        private static readonly Dictionary<string, string> KnownItemCategory = new Dictionary<string, string>(StringComparer.OrdinalIgnoreCase)
        {
            { "Lance Railgun", "Special Weapons" },
            { "Thunderburst Heavy Cannon", "Special Weapons" },
            { "Vulcan Rotary Cannon", "Special Weapons" },
            { "CX-305 Sideclip", "Weapons" },
            { "VSR Halberd", "Weapons" },
            { "SR.99 Javelin", "Weapons" },
            { "Ironbelt LMG", "Weapons" },
            { "Bulldog-SA7", "Weapons" },
            { "Stinger MP-75", "Weapons" },
            { "Fragment Cannon", "Pilot Cannons" },
            { "Fortress Shield", "Shield Generators" },
            // Confirmed via a real "Dump Module Kinds" log (Editor_Log
            // shields fix.txt) - there are several distinct Shield
            // Generators templates, not just Fortress Shield.
            { "Microsoft™ Defender", "Shield Generators" },
            { "Fighter Shield", "Shield Generators" },
            { "Skirmisher Shield", "Shield Generators" },
        };

        private Dictionary<string, (string group, string name)> GetCategoryMap() => CategoryByGuid;

        // There's no separately-extracted "item database" file for this game -
        // everything the mod knows comes from reflecting the live running game,
        // same as the module catalog. This pulls the real m_CategoryGuid for
        // EVERY blueprint you currently own, groups them by guid so you can see
        // exactly which items share a category, does a one-time full shape dump
        // of blueprint[0] + its m_GeneratedData (looking for any field that
        // might be a more authoritative category indicator than m_CategoryGuid
        // alone), and cross-checks m_BlueprintSlotCapacities against
        // CategoryByGuid. Run this again (Diagnostics -> Dump Categories) any
        // time a new item shows up with an "UNMAPPED" category guid, and send
        // me the log so I can add it to CategoryByGuid.
        private void DumpAllBlueprintCategories()
        {
            var blueprints = GetBlueprintsSnapshot();
            Log($"========== DUMPING CATEGORY INFO FOR ALL {blueprints.Count} BLUEPRINT(S) ==========");
            Log("Format: [index] name | categoryGuid | slot | moduleCount | currently-assumed group/category");
            var categoryMap = GetCategoryMap();

            for (int i = 0; i < blueprints.Count; i++)
            {
                object bp = blueprints[i];
                object generatedData = GetInstanceMemberValue(bp, "m_GeneratedData");
                string name = AsString(GetInstanceMemberValue(generatedData, "ResolvedName"));
                string categoryGuid = GetInstanceMemberValue(bp, "m_CategoryGuid") as string;
                object slot = GetInstanceMemberValue(bp, "m_SlotIndex");
                int moduleCount = GetModuleCount(generatedData);

                string assumedGroup = "?", assumedCategory = "?";
                if (KnownItemCategory.TryGetValue(name ?? "", out var known)) { assumedGroup = known == "Weapons" ? "Equipment" : "Components"; assumedCategory = known + " (name override)"; }
                else if (categoryGuid != null && categoryMap.TryGetValue(categoryGuid, out var info)) { assumedGroup = info.group; assumedCategory = info.name; }

                Log($"  [{i}] {name} | categoryGuid={categoryGuid} | slot={SafeInt(slot)} | modules={moduleCount} | assumed: {assumedGroup}/{assumedCategory}");

                if (i == 0)
                {
                    Log("One-time diagnostic: full shape of blueprint[0] and its m_GeneratedData - looking for any field/property that might be a more authoritative category/slot-type indicator than m_CategoryGuid alone.");
                    DumpValueShapeAndValues(bp, "blueprint[0]");
                    DumpValueShapeAndValues(generatedData, "blueprint[0].m_GeneratedData");
                }
            }

            Log("---- distinct categoryGuid -> item name(s) sharing it (use this to sanity-check the positional guess below) ----");
            var byGuid = new Dictionary<string, List<string>>();
            for (int i = 0; i < blueprints.Count; i++)
            {
                object bp = blueprints[i];
                object generatedData = GetInstanceMemberValue(bp, "m_GeneratedData");
                string name = AsString(GetInstanceMemberValue(generatedData, "ResolvedName"));
                string categoryGuid = GetInstanceMemberValue(bp, "m_CategoryGuid") as string ?? "(null)";
                if (!byGuid.TryGetValue(categoryGuid, out var list)) { list = new List<string>(); byGuid[categoryGuid] = list; }
                if (!list.Contains(name)) list.Add(name);
            }
            foreach (var kv in byGuid) Log($"  {kv.Key} -> {string.Join(", ", kv.Value)}");

            Log("---- m_BlueprintSlotCapacities in order (cross-check against the guid-keyed CategoryByGuid table) ----");
            var caps = GetBlueprintSlotCapacities();
            for (int i = 0; i < caps.Count; i++)
            {
                string guid = GetInstanceMemberValue(caps[i], "m_CategoryGuid") as string;
                string resolved = (guid != null && CategoryByGuid.TryGetValue(guid, out var info)) ? $"{info.group}/{info.name}" : "UNMAPPED - tell me this guid + an item name that has it";
                bool seenAmongOwnedItems = guid != null && byGuid.ContainsKey(guid);
                Log($"  [{i}] categoryGuid={guid} -> {resolved} (seen among your owned items: {seenAmongOwnedItems})");
            }
            Log("========== END CATEGORY DUMP ==========");
        }

        // We already know ItemModuleScriptable has m_AllowedItems/
        // m_ForbiddenItems fields (seen in the sample-module shape dump), but
        // we've never actually looked INSIDE them - don't know the element
        // type, and don't know whether "ship" vs "on-foot" is even
        // represented there or somewhere else entirely (a school enum,
        // maybe). Also checks whether module display names are ever
        // duplicated across multiple guids (e.g. "Adaptive Viral Payload"
        // possibly existing once for on-foot items and once for ship-mounted
        // ones, with different ranges) - that would explain the
        // context-dependent stats directly. Run this before implementing any
        // ship/on-foot filtering, not after guessing at it.
        private void DumpModuleCompatibility()
        {
            if (_moduleCandidates.Count == 0) RefreshModuleCandidates(false);
            Log($"========== DUMPING MODULE COMPATIBILITY INFO ({_moduleCandidates.Count} candidate(s)) ==========");

            var byName = new Dictionary<string, List<ModuleCandidate>>(StringComparer.OrdinalIgnoreCase);
            foreach (var c in _moduleCandidates)
            {
                if (!byName.TryGetValue(c.DisplayName, out var list)) { list = new List<ModuleCandidate>(); byName[c.DisplayName] = list; }
                list.Add(c);
            }
            var duplicates = new List<KeyValuePair<string, List<ModuleCandidate>>>();
            foreach (var kv in byName) if (kv.Value.Count > 1) duplicates.Add(kv);

            Log($"---- {duplicates.Count} display name(s) with more than one module entry (out of {byName.Count} distinct names) ----");
            foreach (var kv in duplicates)
            {
                Log($"  '{kv.Key}': {kv.Value.Count} entries");
                foreach (var c in kv.Value) Log($"    guid={c.Guid}  rarityRange={GetRarityRangeString(c.Scriptable)}");
            }

            // Deep-dump m_AllowedItems/m_ForbiddenItems for a handful of
            // samples - prefer a duplicate-named pair if we found one, since
            // that's the case that actually matters for this question.
            var samples = new List<ModuleCandidate>();
            if (duplicates.Count > 0) samples.AddRange(duplicates[0].Value);
            for (int i = 0; samples.Count < 4 && i < _moduleCandidates.Count; i++)
                if (!samples.Contains(_moduleCandidates[i])) samples.Add(_moduleCandidates[i]);

            foreach (var c in samples)
            {
                Log($"---- Allowed/Forbidden items for '{c.DisplayName}' (guid={c.Guid}) ----");
                object allowed = GetInstanceMemberValue(c.Scriptable, "m_AllowedItems");
                object forbidden = GetInstanceMemberValue(c.Scriptable, "m_ForbiddenItems");
                DumpListContents(allowed, "m_AllowedItems");
                DumpListContents(forbidden, "m_ForbiddenItems");
            }
            Log("========== END MODULE COMPATIBILITY DUMP ==========");
        }

        // User asked whether custom module stats have real RNG variation (a
        // range each roll can land in), not just a fixed number per rarity.
        // A one-time diagnostic from earlier this session already confirmed
        // the real shape: ItemModuleTweakableValue has m_BaseValueMin,
        // m_BaseValueMax, m_ValuePerUpgrade, m_RoundToNearest, and a
        // Single CalculateRolledValue(...) method - the official function
        // that turns a raw 0-1 roll (module.m_BaseValueRolls[i], already
        // used by Reroll) plus the module's upgrade level into the real
        // displayed stat value. This confirms the exact method signature
        // (only the 2-parameter COUNT was known before, not the parameter
        // types), and for actual equipped Custom Modules shows the real
        // min/max range alongside the module's current roll and computed
        // value, so it's visible whether roll=0 vs roll=1 genuinely produce
        // different numbers (real RNG) before adding a "range: X - Y"
        // display to the GUI for these.
        private void DumpModuleValueRangeDiscovery()
        {
            Log("========== MODULE VALUE RANGE DISCOVERY ==========");

            if (_moduleCandidates.Count == 0) RefreshModuleCandidates(false);

            Type tweakableType = FindType("Il2CppKeepsake.HyperSpace.System.Modifiers.ItemModule.ItemModuleTweakableValue");
            if (tweakableType == null)
            {
                Log("ItemModuleTweakableValue type not found.");
                Log("========== END MODULE VALUE RANGE DISCOVERY ==========");
                return;
            }

            MethodInfo calcMethod = null;
            foreach (var m in tweakableType.GetMethods(BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Instance))
            {
                if (m.Name != "CalculateRolledValue") continue;
                var ps = new List<string>();
                foreach (var p in m.GetParameters()) ps.Add(p.ParameterType.Name + " " + p.Name);
                Log($"  CalculateRolledValue signature: {m.ReturnType.Name} CalculateRolledValue({string.Join(", ", ps)})");
                if (m.GetParameters().Length == 2) calcMethod = m;
            }
            if (calcMethod == null) Log("  No 2-parameter CalculateRolledValue overload found - will still show min/max/roll below, just not the computed value.");

            var blueprints = GetBlueprintsSnapshot();
            int shown = 0;
            foreach (var bp in blueprints)
            {
                if (shown >= 6) break;
                object generatedData = GetInstanceMemberValue(bp, "m_GeneratedData");
                string itemName = AsString(GetInstanceMemberValue(generatedData, "ResolvedName"));
                int moduleCount = GetModuleCount(generatedData);
                for (int m = 0; m < moduleCount && shown < 6; m++)
                {
                    object module = GetModuleAt(generatedData, m);
                    string moduleGuid = GetInstanceMemberValue(module, "m_ModuleGuid") as string;
                    var candidate = FindCandidateByGuid(moduleGuid);
                    if (candidate == null || candidate.IsBasicModule) continue; // Custom Modules only - Upgradeable Features always match item rarity, no independent roll

                    object rarity = GetInstanceMemberValue(module, "m_Rarity");
                    object upgradeLevelObj = GetInstanceMemberValue(module, "m_UpgradeLevel");
                    int upgradeLevel = upgradeLevelObj is int ul ? ul : 0;
                    float[] rolls = ReadFloatArray(GetInstanceMemberValue(module, "m_BaseValueRolls"));

                    Log($"---- \"{itemName}\" module[{m}] '{candidate.DisplayName}' rarity={rarity} upgradeLevel={upgradeLevel} rolls=[{string.Join(", ", rolls)}] ----");

                    MethodInfo getTweakables = null;
                    foreach (var gm in candidate.Scriptable.GetType().GetMethods(BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Instance))
                    {
                        if (gm.Name == "GetTweakableValuesForRarity" && gm.GetParameters().Length == 1) { getTweakables = gm; break; }
                    }
                    object list = null;
                    try { list = getTweakables?.Invoke(candidate.Scriptable, new object[] { rarity }); }
                    catch (Exception ex) { Log("    GetTweakableValuesForRarity threw: " + ex.Message); }
                    var entries = list == null ? new List<object>() : ReadIndexedCollection(list);

                    for (int t = 0; t < entries.Count; t++)
                    {
                        object tw = entries[t];
                        string twName = GetInstanceMemberValue(tw, "m_Name") as string;
                        object minV = GetInstanceMemberValue(tw, "m_BaseValueMin");
                        object maxV = GetInstanceMemberValue(tw, "m_BaseValueMax");
                        object perUpg = GetInstanceMemberValue(tw, "m_ValuePerUpgrade");
                        object roundTo = GetInstanceMemberValue(tw, "m_RoundToNearest");
                        Log($"    tweakable[{t}] '{twName}' min={minV} max={maxV} perUpgrade={perUpg} roundToNearest={roundTo}");

                        if (calcMethod != null && t < rolls.Length)
                        {
                            try
                            {
                                object atRoll = calcMethod.Invoke(tw, new object[] { rolls[t], upgradeLevel });
                                object atMin = calcMethod.Invoke(tw, new object[] { 0f, upgradeLevel });
                                object atMax = calcMethod.Invoke(tw, new object[] { 1f, upgradeLevel });
                                Log($"      CalculateRolledValue: at this roll ({rolls[t]}) = {atRoll}  |  full range at this upgrade level: roll=0 -> {atMin}, roll=1 -> {atMax}");
                            }
                            catch (Exception ex) { Log("      CalculateRolledValue invoke threw: " + ex.Message); }
                        }
                    }
                    shown++;
                }
            }

            if (shown == 0) Log("  No equipped Custom Modules found across the first few blueprints to sample from.");
            Log("Send this log along - if roll=0 and roll=1 produce genuinely different numbers, that confirms real RNG variation, and this shows the exact fields/method needed to add a 'range: X - Y' display to each Custom Module row in the GUI.");
            Log("========== END MODULE VALUE RANGE DISCOVERY ==========");
        }

        // Checks what the game ACTUALLY uses for "Upgradeable Features" vs
        // "Custom Modules" section placement on every owned item: each
        // equipped module's own m_IsBasicModule flag, cross-referenced
        // against its slot index. This is what surfaced that the
        // basic-slot count isn't a universal constant (Reactors: 1 basic
        // slot; most weapons: 2) - run this any time module section
        // placement looks wrong in-game, or before changing the
        // basic/custom logic again.
        private void DumpModuleKinds()
        {
            var blueprints = GetBlueprintsSnapshot();
            if (_moduleCandidates.Count == 0) RefreshModuleCandidates(false);

            Log($"========== DUMPING MODULE KINDS (basic/Upgradeable Features vs custom/Custom Modules) FOR {blueprints.Count} BLUEPRINT(S) ==========");

            // Per-category summary: what basic-slot counts actually show up,
            // so a pattern like "Reactors always have 1" is visible at a
            // glance instead of having to read every single item line.
            var basicCountsByCategory = new Dictionary<string, List<int>>();

            foreach (var bp in blueprints)
            {
                object generatedData = GetInstanceMemberValue(bp, "m_GeneratedData");
                string name = AsString(GetInstanceMemberValue(generatedData, "ResolvedName"));
                object rarity = GetInstanceMemberValue(generatedData, "m_Rarity");
                string categoryGuid = GetInstanceMemberValue(bp, "m_CategoryGuid") as string;
                string categoryLabel = categoryGuid ?? "(no category guid)";
                if (name != null && KnownItemCategory.TryGetValue(name, out var known)) categoryLabel = known;
                else if (categoryGuid != null && GetCategoryMap().TryGetValue(categoryGuid, out var info)) categoryLabel = info.name;

                int moduleCount = GetModuleCount(generatedData);
                int basicCount = 0, customCount = 0, unmatchedCount = 0;
                var parts = new List<string>();
                for (int m = 0; m < moduleCount; m++)
                {
                    object module = GetModuleAt(generatedData, m);
                    string mGuid = GetInstanceMemberValue(module, "m_ModuleGuid") as string;
                    var cand = FindCandidateByGuid(mGuid);
                    if (cand == null) { unmatchedCount++; parts.Add($"[{m}]?"); continue; }
                    if (cand.IsBasicModule) basicCount++; else customCount++;
                    parts.Add($"[{m}]{(cand.IsBasicModule ? "BASIC" : "custom")}:{cand.DisplayName}");
                }

                Log($"  {name} (category={categoryLabel}, rarity={rarity}, total={moduleCount}, basic={basicCount}, custom={customCount}{(unmatchedCount > 0 ? $", unmatched={unmatchedCount}" : "")}): {string.Join("  ", parts)}");

                if (!basicCountsByCategory.TryGetValue(categoryLabel, out var list)) { list = new List<int>(); basicCountsByCategory[categoryLabel] = list; }
                list.Add(basicCount);
            }

            Log("---- basic (Upgradeable Features) slot count seen per category ----");
            foreach (var kv in basicCountsByCategory)
            {
                var distinct = new List<int>();
                foreach (var v in kv.Value) if (!distinct.Contains(v)) distinct.Add(v);
                distinct.Sort();
                string consistency = distinct.Count == 1 ? "consistent" : "VARIES - check the per-item lines above";
                Log($"  {kv.Key}: basic count(s) seen = [{string.Join(", ", distinct)}] across {kv.Value.Count} item(s) ({consistency})");
            }
            Log("========== END MODULE KINDS DUMP ==========");
        }

        private void DumpListContents(object list, string label)
        {
            if (list == null) { Log($"  {label} = null"); return; }
            var items = ReadIndexedCollection(list);
            Log($"  {label}: {items.Count} item(s), container type={list.GetType().FullName}");
            for (int i = 0; i < Math.Min(items.Count, 10); i++)
            {
                object item = items[i];
                if (item == null) { Log($"    [{i}] = null"); continue; }
                var t = item.GetType();
                if (t.IsEnum || t.IsPrimitive || item is string) Log($"    [{i}] = {item}  ({t.Name})");
                else DumpValueShapeAndValues(item, $"    {label}[{i}]");
            }
            if (items.Count > 10) Log($"  ... and {items.Count - 10} more");
        }

        private static Type FindType(string fullName)
        {
            foreach (var asm in AppDomain.CurrentDomain.GetAssemblies())
            {
                Type[] types;
                try { types = asm.GetTypes(); }
                catch (ReflectionTypeLoadException rtle)
                {
                    // Partial load failure is common in these huge auto-generated
                    // interop assemblies - most types still resolved fine, so use
                    // those instead of throwing the whole assembly away.
                    var loaded = new List<Type>();
                    foreach (var t in rtle.Types) if (t != null) loaded.Add(t);
                    types = loaded.ToArray();
                }
                catch { continue; }

                foreach (var t in types)
                {
                    if (t.FullName == fullName) return t;
                }
            }
            return null;
        }

        private static object GetStaticMemberValue(Type t, string name)
        {
            var prop = t.GetProperty(name, BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Static);
            if (prop != null) { try { return prop.GetValue(null); } catch { return null; } }
            var field = t.GetField(name, BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Static);
            if (field != null) { try { return field.GetValue(null); } catch { return null; } }
            return null;
        }

        private static object GetInstanceMemberValue(object obj, string name)
        {
            if (obj == null) return null;
            var t = obj.GetType();
            var prop = t.GetProperty(name, BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Instance);
            if (prop != null) { try { return prop.GetValue(obj); } catch { return null; } }
            var field = t.GetField(name, BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Instance);
            if (field != null) { try { return field.GetValue(obj); } catch { return null; } }
            return null;
        }

        // Writes a value back onto a named property/field of obj, logging the
        // reason on failure instead of swallowing it silently. Needed anywhere
        // we've pulled a struct (GeneratedItem/GeneratedModule are almost
        // certainly C# structs - see the comment above HandleSetRarity) out of
        // a parent object: GetInstanceMemberValue hands back a boxed COPY in
        // that case, so mutating the copy alone never touches the real data -
        // it has to be explicitly written back into whatever field it came from.
        private bool TrySetInstanceMemberValue(object obj, string name, object value)
        {
            if (obj == null) { Log($"TrySetInstanceMemberValue({name}): target object is null."); return false; }
            var t = obj.GetType();
            var prop = t.GetProperty(name, BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Instance);
            if (prop != null)
            {
                if (!prop.CanWrite)
                {
                    Log($"TrySetInstanceMemberValue({name}): property found on {t.FullName} but CanWrite=false.");
                }
                else
                {
                    try { prop.SetValue(obj, value); return true; }
                    catch (Exception ex) { Log($"TrySetInstanceMemberValue({name}): property SetValue threw: {ex.Message}"); }
                }
            }
            var field = t.GetField(name, BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Instance);
            if (field != null)
            {
                try { field.SetValue(obj, value); return true; }
                catch (Exception ex) { Log($"TrySetInstanceMemberValue({name}): field SetValue threw: {ex.Message}"); }
            }
            if (prop == null && field == null) Log($"TrySetInstanceMemberValue({name}): no property or field with that name found on {t.FullName}.");
            return false;
        }

        // Writes a (mutated, boxed-copy) module struct back into the m_Modules
        // array it came from, via the array's set_Item - the array itself is a
        // reference type, so this is the one write that's guaranteed to be
        // visible everywhere else that reads the same array, regardless of
        // whether GeneratedItem/generatedData copies above it are stale.
        private bool TryWriteModuleBack(object generatedData, int moduleIndex, object mutatedModule)
        {
            object modules = GetInstanceMemberValue(generatedData, "m_Modules");
            if (modules == null) { Log("TryWriteModuleBack: m_Modules is null."); return false; }
            var itemProp = modules.GetType().GetProperty("Item", BindingFlags.Public | BindingFlags.Instance);
            if (itemProp == null) { Log("TryWriteModuleBack: m_Modules has no Item property."); return false; }
            if (!itemProp.CanWrite) { Log("TryWriteModuleBack: m_Modules.Item has no setter (CanWrite=false) - array type " + modules.GetType().FullName + "."); return false; }
            try { itemProp.SetValue(modules, mutatedModule, new object[] { moduleIndex }); return true; }
            catch (Exception ex) { Log($"TryWriteModuleBack: set_Item({moduleIndex}) threw: {ex.Message}"); return false; }
        }

        private static string AsString(object obj)
        {
            var s = obj as string;
            return s ?? "?";
        }

        private void Log(string message)
        {
            MelonLogger.Msg(message);
            try
            {
                var dir = Path.GetDirectoryName(Assembly.GetExecutingAssembly().Location);
                var path = Path.Combine(dir ?? ".", "Editor_Log.txt");
                File.AppendAllText(path, $"[{DateTime.Now:HH:mm:ss}] {message}{Environment.NewLine}");
            }
            catch { }
        }
    }
}
