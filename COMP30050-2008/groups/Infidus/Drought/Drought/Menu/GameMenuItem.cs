using System;
using System.Collections.Generic;
using System.Text;
using Microsoft.Xna.Framework.Graphics;
using Drought.Network;

namespace Drought.Menu
{
    class GameMenuItem : MenuItem 
    {
        private RemoteGame remoteGame;

        public GameMenuItem(MenuFunctions function, String text, SpriteFont font, RemoteGame game)
            : base(function, text, font) {
            remoteGame = game;
        }

        public RemoteGame getGame() {
            return remoteGame;
        }
    }
}
