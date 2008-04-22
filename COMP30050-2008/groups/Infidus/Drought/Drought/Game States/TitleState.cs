using System;
using System.Collections.Generic;
using System.Text;
using Drought.GameStates;
using Drought.State;
using Microsoft.Xna.Framework;
using Drought.World;

namespace Drought.Game_States
{
    class TitleState : LevelState
    {
        public TitleState(IStateManager manager, DroughtGame game, Level aLevel) :
            base(manager, game, aLevel)
        {

        }

        public override void update(GameTime gameTime)
        {
            sun.update(gameTime);
            rain.update();
        }

        public Camera getCamera()
        {
            return camera;
        }
    }
}
