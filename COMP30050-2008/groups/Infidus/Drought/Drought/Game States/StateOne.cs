using System;
using System.Collections.Generic;
using System.Text;
using Microsoft.Xna.Framework;
using Microsoft.Xna.Framework.Graphics;
using Microsoft.Xna.Framework.Content;
using Drought.State;
using Drought.Input;

namespace Drought.GameStates
{
    public class StateOne : GameState
    {
        private Input.Input input;

        public StateOne(IStateManager manager, Game game)
            : base(manager, game)
        {
            input = Input.Input.getInput();
        }

        public override void loadContent()
        {
            
        }

        public override void background()
        {
            Console.WriteLine("StateOne background");
        }

        public override void foreground()
        {
            Console.WriteLine("StateOne foreground");
        }

        public override void update(GameTime gameTime)
        {
            if (input.isKeyPressed(GameKeys.CHANGE_STATE))
                getStateManager().pushState(new StateTwo(getStateManager(), getGame()));

        }

        public override void render(GraphicsDevice graphics, SpriteBatch spriteBatch)
        {
            graphics.Clear(Color.Black);
        }
    }
}
