using System;
using Microsoft.Xna.Framework.Graphics;
using Drought.Network;
using Drought.World;

namespace Drought.Menu
{
    class LevelMenuItem : MenuItem 
    {
        private Level level;

        public LevelMenuItem(MenuFunctions function, String text, SpriteFont font, Level aLevel)
            : base(function, text, font)
        {
            level = aLevel;
        }

        public Level getLevel()
        {
            return level;
        }
    }

    class JoinLevelMenuItem : LevelMenuItem
    {
        private RemoteGame remoteGame;

        public JoinLevelMenuItem(MenuFunctions function, String text, SpriteFont font, Level aLevel, RemoteGame game)
            : base(function, text, font, aLevel)
        {
            remoteGame = game;
        }

        public RemoteGame getGame()
        {
            return remoteGame;
        }
    }
}
