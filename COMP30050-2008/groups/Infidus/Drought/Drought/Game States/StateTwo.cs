using System;
using System.Collections.Generic;
using System.Text;
using Microsoft.Xna.Framework;
using Microsoft.Xna.Framework.Graphics;
using Microsoft.Xna.Framework.Content;

namespace drought_states
{
    public class StateTwo : GameState
    {
        private Input input;

        public StateTwo(IStateManager manager, ContentManager content)
            : base(manager, content)
        {
            input = Input.getInput();
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

        public override void render(GraphicsDeviceManager graphics, SpriteBatch spriteBatch)
        {
            graphics.GraphicsDevice.Clear(Color.Red);
        }
    }
}
