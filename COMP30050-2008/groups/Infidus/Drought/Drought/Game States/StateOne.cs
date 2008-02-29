using System;
using System.Collections.Generic;
using System.Text;
using Microsoft.Xna.Framework;
using Microsoft.Xna.Framework.Graphics;
using Microsoft.Xna.Framework.Content;

namespace drought_states
{
    public class StateOne : GameState
    {
        private Input input;

        public StateOne(IStateManager manager, ContentManager content)
            : base(manager, content)
        {
            input = Input.getInput();
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
                getStateManager().pushState(new StateTwo(getStateManager(), getContentManager()));

        }

        public override void render(GraphicsDeviceManager graphics, SpriteBatch spriteBatch)
        {
            graphics.GraphicsDevice.Clear(Color.Black);
        }
    }
}
