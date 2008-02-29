using System;
using System.Collections.Generic;
using System.Text;
using Microsoft.Xna.Framework;
using Microsoft.Xna.Framework.Graphics;
using Microsoft.Xna.Framework.Content;

namespace drought_states
{

    public abstract class GameState
    {
        /** The <code>StateManager</code> managing this state */
        private IStateManager stateManager;

        /** The content manager for this state to use to load content */
        private ContentManager content;
        
        /**
         * Constructs a new <code>GameState</code> being managed by
         * the specified <code>StateManager</code> class.
         * 
         * @param manager The state manager to manage this state.
         */
        public GameState(IStateManager manager, ContentManager content)
        {
            stateManager = manager;
            this.content = content;
            loadContent();
        }

        /**
         * This method is called once when a state is created
         * and if the game requires its content to be reloaded.
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
         * be used to draw any sprites. It is guaranteed that spriteBatch will be
         * inbetween a Begin() and End() call, so sprites can be drawn without calling
         * these functions. This is to cut down on the number of Begin()/End() calls
         * as they can decrease performance. If it is required to call End() in order to
         * draw sprites with different properties, it must be ensured that when the
         * render call completes, spriteBatch is between a Begin()/End() call and has its
         * default properties.
         * 
         * @param graphics The graphics device manager to draw with.
         * @param spriteBatch A sprite batch to use to draw sprites.
         */
        public abstract void render(GraphicsDeviceManager graphics, SpriteBatch spriteBatch);
        
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
    }
}