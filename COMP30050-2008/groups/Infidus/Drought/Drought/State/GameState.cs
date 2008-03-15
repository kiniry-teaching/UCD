using System;
using System.Collections.Generic;
using System.Text;
using Microsoft.Xna.Framework;
using Microsoft.Xna.Framework.Graphics;
using Microsoft.Xna.Framework.Content;

namespace Drought.State
{

    public abstract class GameState
    {
        /** The <code>StateManager</code> managing this state */
        private IStateManager stateManager;

        /** The game that this state is running on */
        private Game game;

        /** The content manager for this state to use to load content */
        private ContentManager content;

        /** The game's graphics device provided by XNA */
        private GraphicsDevice graphics;

        /** The game's sprite batch used when sprite drawing is required */
        private SpriteBatch spriteBatch;

        public GameState() { }

        /**
         * Constructs a new <code>GameState</code> being managed by
         * the specified <code>StateManager</code> class.
         * 
         * @param manager The state manager to manage this state.
         * @param game XNA's game class to get accesses to 
         *      resource managers and devices.
         */
        public GameState(IStateManager manager, Game game)
        {
            this.game = game;
            stateManager = manager;
            this.content = game.Content;
            this.graphics = game.GraphicsDevice;
            this.spriteBatch = ((Game1)game).getSpriteBatch();
        }

        /**
         * This method is called if the game requires its content to be reloaded.
         * This occurrs when XNA calls LoadContent().
         */
        public abstract void loadContent();
        
        /**
         * Logic to execute when another state is pushed on top of this one in the
         * state manager's stack.
         */
        public abstract void background();

        /**
         * Logic to execute when this state becomes the state on top of the state
         * from either being pushed onto the stack or a state above it being popped
         * off the stack.
         */
        public abstract void foreground();

        /**
         * Logic to be executed each time the game loops.
         * 
         * @param gameTime The current game time.
         */
        public abstract void update(GameTime gameTime);

        /**
         * Called to render the state to the screen. The graphics device manager
         * can be used to draw graphical content and the spriteBatch can
         * be used to draw any sprites.
         * 
         * @param graphics The graphics device manager to draw with.
         * @param spriteBatch A sprite batch to use to draw sprites.
         */
        public abstract void render(GraphicsDevice graphics, SpriteBatch spriteBatch);
        
        /**
         * Gets the <code>StateManager</code> that is managing this state.
         * 
         * @return State's manager.
         */
        public IStateManager getStateManager()
        {
            return stateManager;
        }

        /**
         * Gets the ContentManager to use to load any required
         * content.
         * 
         * @return The content manager.
         */
        public ContentManager getContentManager()
        {
            return content;
        }

        public GraphicsDevice getGraphics()
        {
            return graphics;
        }

        public SpriteBatch getSpriteBatch()
        {
            return spriteBatch;
        }

        public Game getGame()
        {
            return game;
        }
    }
}
