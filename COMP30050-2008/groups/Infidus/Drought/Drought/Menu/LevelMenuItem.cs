using System;
using Microsoft.Xna.Framework.Graphics;
using Drought.Network;
using Drought.World;

namespace Drought.Menu
{
    class LevelMenuItem : MenuItem 
    {
        Level level;

        public LevelMenuItem(MenuFunctions function, String text, SpriteFont font, Level level)
            : base(function, text, font) {
            this.level = level;
        }

        public Level getLevel()
        {
            return level;
        }
    }

    class JoinLevelMenuItem : LevelMenuItem
    {
        private RemoteGame remoteGame;
        public JoinLevelMenuItem(MenuFunctions function, String text, SpriteFont font, Level level, RemoteGame game)
            : base(function, text, font, level) {
            remoteGame = game;
        }

        public RemoteGame getGame() {
            return remoteGame;
        }
    }
}
