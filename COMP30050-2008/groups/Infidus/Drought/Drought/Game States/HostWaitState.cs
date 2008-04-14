using Microsoft.Xna.Framework;
using Microsoft.Xna.Framework.Graphics;
using Drought.State;
using Drought.Network;

namespace Drought.GameStates
{
    /**
     * Waits for another player to join the game, and then pops itself.
     */
    class HostWaitState : GameState
    {
        /**  */
        private IStateManager stateManager;
        
        /** The NetworkManager to wait for a connection on. */
        private NetworkManager networkManager;
        
        /** A texture with the words "waiting for another remote player to join...". */
        private Texture2D waiting;

        /** The position to draw the Texture waiting at so it's centred onscreen. */
        private Vector2 drawPos;

        public HostWaitState(IStateManager manager, DroughtGame game) : base(manager, game)
        {
            stateManager = manager;
            networkManager = game.getNetworkManager();
            loadContent();
        }

        public override void loadContent() {
            waiting = getContentManager().Load<Texture2D>("Textures/waiting");
            int showX = (waiting.GraphicsDevice.Viewport.Width - waiting.Width) / 2;
            int showY = (waiting.GraphicsDevice.Viewport.Height - waiting.Height) / 2;
            drawPos = new Vector2(showX, showY);
        }

        public override void background() { }

        public override void foreground() { }

        public override void update(Microsoft.Xna.Framework.GameTime gameTime)
        {
            if (networkManager.anyoneElseHere()) {
                stateManager.popState();
            }
        }

        public override void render(GraphicsDevice graphics, SpriteBatch spriteBatch) {
            spriteBatch.Begin();
            spriteBatch.Draw(waiting, drawPos, Color.White);
            spriteBatch.End();
        }
    }
}
