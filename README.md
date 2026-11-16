# 📻 MP3Player (Sons of the Forest)

A custom FMOD audio engine and radio replacement mod for **Sons of the Forest**.  
Stream your own `.mp3`, `.wav`, `.ogg`, and `.flac` music through 3D world boomboxes, golf carts, or anywhere on the island using Headphones Mode.

---

## ✨ Features

* **Multiple Audio Formats:** Supports `.mp3`, `.wav`, `.ogg`, and `.flac` files dropped directly into your `Tracks` folder.
* **3 Playback Modes:**
  * **3D World Boomboxes:** Directional spatial audio with distance culling and a custom real-time **3D LCD countdown display** rendered directly onto the boombox screen.
  * **Golf Carts:** Seamless audio handoff when hopping in and out of golf carts without losing your track position.
  * **Headphones Mode (2D):** Listen to your playlists anywhere on the island without needing a radio nearby.
* **Multi-Folder Playlists:** Organize your music into subfolders inside `Mods/mp3player/Tracks/` and cycle through playlists on the fly (`All Playlists`, `Root`, and individual folders).
* **Full Playback Controls:** Play/Pause, Next/Previous track, Fast Forward (+30s), Rewind (-15s), Repeat Single Track, Shuffle, and Integrated Volume Control (automatically defers to *sotfVolumeMod* if installed).
* **Smart Background Fading:** Smoothly fades music out when pausing the game or alt-tabbing to desktop.
* **Live Track Rescanning:** Toggle **Scan Tracks Folder** in the in-game mod menu to add or remove songs without restarting the game.

---

## 🎮 Default Controls

*(All hotkeys can be customized in-game via the **Mods** menu or `UserData/mp3player.cfg`)*

| Action | Default Key | Config Key Name |
| :--- | :--- | :--- |
| **Play / Pause** | `;` (Semicolon) | `PlayPauseKey` |
| **Switch Playlist** | `'` (Apostrophe) | `SwitchPlaylistKey` |
| **Next Track** | `\` (Backslash) | `SkipTrackKey` |
| **Previous Track** | `P` | `PreviousTrackKey` |
| **Fast Forward (+30s)** | `Right Arrow` | `FastForward30sKey` |
| **Rewind (-15s)** | `Left Arrow` | `Rewind15sKey` |
| **Toggle Repeat Track** | `O` | `RepeatTrackKey` |
| **Toggle Shuffle** | `K` | `ShuffleTrackKey` |
| **Volume Up** | `Numpad +` | `VolumeUpKey` |
| **Volume Down** | `Numpad -` | `VolumeDownKey` |

---

## 📥 Installation

1. Install **RedLoader** for *Sons of the Forest*.
2. Download the latest release `.zip` from the **Releases** page (or Nexus Mods).
3. Extract `mp3player.dll` and the `mp3player` folder into `Sons Of The Forest/Mods/`.
4. Drop your audio files into `Sons Of The Forest/Mods/mp3player/Tracks/` (or create subfolders inside `Tracks/` for separate playlists).
5. Launch the game and turn on a boombox, hop in a golf cart, or enable **Wear Headphones** in the in-game Mod Settings!

---

## 🛠️ Building from Source

If you want to compile or maintain this mod for future *Sons of the Forest* updates:

1. **Target Framework:** `.NET 6.0` (Class Library).
2. **Required References:** Game and RedLoader assemblies are excluded from this repository. Point your `.csproj` references to your local *Sons of the Forest* installation:
   * **From `_Redloader/net6/`:**
     * `RedLoader.dll`
     * `SonsSdk.dll`
     * `SUI.dll`
     * `0Harmony.dll`
     * `Il2CppInterop.Runtime.dll`
   * **From `_Redloader/Game/`:**
     * `Assembly-CSharp.dll`
     * `Il2Cppmscorlib.dll`
     * `Il2CppSystem.dll`
     * `UnityEngine.CoreModule.dll`
     * `UnityEngine.UI.dll`
     * `UnityEngine.UIModule.dll`
     * `UnityEngine.TextRenderingModule.dll`
3. **Runtime Bank & Custom FMOD GUIDs:**
   * Keep `CustomRadio.bank` inside `Mods/mp3player/` alongside the compiled `mp3player.dll` in `Mods/`.
   * If you build your own replacement `.bank` in FMOD Studio (with a 3D Programmer Instrument event and a 2D Programmer Instrument event), update the two event GUID constants in `CustomRadioMod.cs` to match your new bank events:
     ```csharp
     public static readonly Il2CppSystem.Guid CustomEventGuid = Il2CppSystem.Guid.Parse("b8306987-8d77-4184-8718-7367879cabbf");
     public static readonly Il2CppSystem.Guid CustomEvent2DGuid = Il2CppSystem.Guid.Parse("{e2379ac8-c6c2-4cdc-8e23-75891c71d08e}");
     ```
