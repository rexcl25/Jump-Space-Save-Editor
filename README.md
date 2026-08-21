
# JumpSpace Blueprint Editor

A tool for editing your Jump Space gear and save while the game is running. Change rarity, level, and modules on your equipment, swap what an item actually is, edit what's in your inventory, and adjust your credits and materials — all from a simple web page.

**Back up your save first**, just in case.

> **Work in progress.** This is a personal modding project, still actively being poked at and fixed. In particular: **inventory (carried item) editing does not currently work correctly** — edits save to disk, but the fix to push them into the live running game session isn't reliable yet, so what you see in-game may not match what the web page shows until you exit and re-enter. Blueprint/assembler equipment editing and currencies are solid.

## A note on cheating

Jump Space is fully co-op with no PvP, and the developer has said as much on the Steam forums: ["we don't intend to care much for cheating since it's a co-op game"](https://steamcommunity.com/app/1757300/discussions/0/4352240067030448723/). This tool only edits your own local save file — it doesn't touch anyone else's data or give any advantage in a competitive sense, since there isn't one. Still, use it in games with people you trust, and don't be surprised if a save edited this way behaves unpredictably around teammates who haven't made the same changes.

## What you need

- [MelonLoader](https://melonwiki.xyz/) installed for Jump Space.

## Setup

1. Launch Jump Space once with MelonLoader installed. This creates a `Mods` folder inside your Jump Space install folder (if it isn't there already).
2. Copy `JumpSpaceEditor.dll` and `EditorUI.html` into that `Mods` folder.
3. Launch (or relaunch) the game.

## How to use it

1. With the game running, open **http://localhost:8765/** in any web browser — a second monitor works great for this.
2. Get into your hangar. Your blueprints and currencies will show up on the page.
3. From there, you can:
   - Change an item's rarity, level, and individual modules (rarity changes are limited to each module's real valid range, same as the "range: X-Y" tag shown next to it)
   - Fine-tune a module's rolled stats with a slider, instead of just rerolling blind
   - Swap what an item's base type is (e.g. turn a Sideclip into a Scorpion)
   - Change a weapon's scope or color
   - Edit your carried inventory (including swapping consumables) — **work in progress, see the note above**
   - Duplicate a blueprint into the next open slot in its category, or permanently delete one — **new and less tested than everything else here; see the note below**
   - Add credits and materials
   - Turn on **Cheat Mode** to push rarity, module level, and stat rolls past what the game normally allows — see the note below
4. Everything saves automatically when you make a change. You can also hit **Save Now** on the page, or press **F6** in-game, any time you want to be sure.

### Backups

The page keeps its own rolling backups of your save file (separate from the game's own cloud sync), in a **Backups** section — a copy is taken automatically the first time you save each session, and you can also hit **Backup Now** any time. Restoring a backup only changes the file on disk right away; because this mod edits a *live* running game, you need to close and reopen your save (or restart the game) afterward to actually see the restored version — your current session won't notice until then.

### Duplicate / Delete

**Newer and less tested than everything else in this tool.** Every other edit here modifies an item that already exists in your save; Duplicate and Delete are the first features that create or remove one outright, which is a step further into unverified territory for this mod. Duplicate copies an item's rarity, level, type, and every module/cosmetic into the next open slot in the same category. Delete removes an item permanently — there's no per-item Reset for it, only a backup restore. If either one doesn't behave as expected, check `Editor_Log.txt` next to the mod DLL and let me know what it says.

### Cheat Mode

A toggle in the toolbar that relaxes three limits this tool normally enforces: rarity is no longer restricted to a module's valid range, a module's stat roll can go up to 300% instead of capping at 100%, and — new — a module's own level can be set directly, bypassing the game's normal upgrade cap (previously there was no way to do this at all; only the whole item's level could be set freely). Turning it on immediately backs up your save, separately from the automatic per-session backup. Values pushed past the game's real limits may behave unpredictably in-game, and the game itself might silently revert some of them on its own. Turning Cheat Mode off doesn't undo anything already written — it just goes back to enforcing the normal limits for anything you change from then on.

### Handy in-game keys

You don't need the web page open for these to work:

- **F6** — Force save
- **F7** — +25,000 credits
- **F8** — Add materials (all tiers at once)

In the browser tab, **F5** refreshes the page.

## Undoing changes

Every module and item has its own "Reset" button. The **Reset Everything** button on the toolbar undoes everything at once, back to how it was when you first opened the page. If you close the tab and lose that starting point, your save backup is the fallback.

## Building from source

Requires the [.NET 6 SDK](https://dotnet.microsoft.com/download/dotnet/6.0). Open `JumpSpaceEditor.csproj`, edit the `<GameDir>` property near the top to point at your own Jump Space install folder, then run:

```
dotnet build -c Release
```

This builds `JumpSpaceEditor.dll` into `build\` and, if your `<GameDir>` is set correctly, automatically copies it (plus `EditorUI.html`) straight into your game's `Mods` folder. Close the game first — a running MelonLoader instance keeps the old DLL locked.

## License

[MIT](LICENSE) - do whatever you want with it.
