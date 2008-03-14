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
    public class StateTwo : GameState
    {
        private Input.Input input;

        public StateTwo(IStateManager manager, Game game)
            : base(manager, game)
        {
            input = Input.Input.getInput();
        }

        public override void loadContent()
        {

        }

        public override void background()
        {
            Console.WriteLine("StateTwo background");
        }

        public override void foreground()
        {
            Console.WriteLine("StateTwo foreground");
        }

        public override void update(GameTime time)
        {
            if (input.isKeyPressed(GameKeys.CHANGE_STATE))
                getStateManager().popState();

        }

        public override void render(GraphicsDevice graphics, SpriteBatch spriteBatch)
        {
            graphics.Clear(Color.Red);
        }
    }
}
