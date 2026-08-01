
# JumpSpace Blueprint Editor

A tool for editing your Jump Space gear and save while the game is running. Change rarity, level, and modules on your equipment, swap what an item actually is, edit what's in your inventory, and adjust your credits and materials — all from a simple web page.

**Back up your save first**, just in case.

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
   - Edit your carried inventory (including swapping consumables)
   - Add credits and materials
4. Everything saves automatically when you make a change. You can also hit **Save Now** on the page, or press **F6** in-game, any time you want to be sure.

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
