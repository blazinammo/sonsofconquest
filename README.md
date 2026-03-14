# Age of Realms – Multiplayer RTS

A browser-based multiplayer real-time strategy game inspired by Age of Empires, built with Three.js, Socket.io, and Node.js.

## Features

- 🌍 Procedurally generated terrain (grass, sand, water, rock)
- 🪵 4 resource types: Wood (trees), Stone, Gold, Food (berry bushes)
- ⚔️ Multiplayer lobbies with up to 4 players (2 per team)
- 🏰 Buildings: Town Center, Barracks, House, Watchtower
- 👷 Units: Villagers (gather resources, build) and Warriors (combat)
- 🗺️ Minimap with camera pan
- 💬 Team chat
- 🎮 Full RTS controls (click, drag, right-click commands)

## Quick Start

### Install dependencies:
```bash
npm install
```

### Run locally:
```bash
npm start
```
Open [http://localhost:3000](http://localhost:3000)

### Development (auto-reload):
```bash
npm run dev
```

## Deploy to Render

1. Push to a GitHub repository
2. Create a new **Web Service** on [render.com](https://render.com)
3. Connect your repository
4. Set:
   - **Build Command**: `npm install`
   - **Start Command**: `npm start`
   - **Environment**: Node
5. Deploy!

## Controls

| Control | Action |
|---------|--------|
| Left Click | Select unit/building |
| Right Click | Move / Attack / Gather |
| Shift + Click | Add to selection |
| WASD / Arrow Keys | Pan camera |
| Scroll Wheel | Zoom |
| B | Open build menu |
| Escape | Deselect / Close menu |
| Enter | Focus chat |

## Gameplay

1. **Enter your name** and create or join a lobby
2. **Choose a team** (Blue = Team 1, Red = Team 2)
3. Host clicks **Begin Battle** to start
4. **Select villagers** and right-click resources to gather
5. **Build structures**: Select villagers → Press B → Choose building → Click to place
6. **Train warriors** by selecting a Barracks and clicking Train
7. **Attack enemies**: Select warriors → Right-click enemy units/buildings
8. **Win** by destroying the enemy Town Center!

## Project Structure

```
aoe-game/
├── server/
│   └── index.js       # Game server (Socket.io, game logic)
├── public/
│   ├── index.html     # UI, HUD, lobby screens
│   └── js/
│       └── game.js    # Three.js renderer, input, client logic
├── package.json
└── README.md
```
