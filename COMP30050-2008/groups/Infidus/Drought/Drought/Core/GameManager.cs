using System;
using System.Collections.Generic;
using System.Text;
using Microsoft.Xna.Framework;
using Microsoft.Xna.Framework.Graphics;
using Drought.State;

namespace Drought
{
    class GameManager : IStateManager
    {
        /** Possible state change operations used when storing changes */
        private enum changeOperation { PUSH, POP };

        /** Stack of game states */
        private List<GameState> stateStack;

        /** The XNA game class for callbacks */
        private Game game;

        #region state changing data
        /*
         * Any requests to change the state stack must be stored
         * and executed only after update calles to states have
         * completed. This enables the foregound() and backgound()
         * functions to be called at the correct time.
         */

        /** Stores requests to change the state stack */
        private List<ChangeInfo> changes;

        /** Stores information about a state change request */
        private struct ChangeInfo
        {
            /** The type of request */
            public changeOperation operation;

            /** The state to change to or null if a pop request */
            public GameState state;

            /**
             * Constructs a new struct representing a state change
             * request.
             * 
             * @param state The state to change to or null of pop is requested.
             * @param operation The operation to perform.
             */
            public ChangeInfo(GameState state, changeOperation operation)
            {
                this.state = state;
                this.operation = operation;
            }
        }
        #endregion


        /**
         * Constructs a new <CODE>GameManager</CODE>
         */
        public GameManager(Game game)
        {
            stateStack = new List<GameState>();
            changes = new List<ChangeInfo>();
            this.game = game;
        }
         
        /**
         * Processes any pending state change requests and updates
         * the current game state.
         * 
         * @param gameTime The current game time.
         */
        public void update(GameTime gameTime)
        {
            doChanges();

            /**
             * Only update if there exists a state on the stack.
             * A situation where the stack is empty can occurr
             * when trying to exit. XNA won't exit at the call
             * to Exit(), instead it will wait until the next 
             * game loop to exit.
             */
            if(stateStack.Count > 0)
                stateStack[stateStack.Count - 1].update(gameTime);
        }

        /**
         * Renders the current game state.
         * 
         * @param graphics The graphics device to render to.
         */
        public void render(GraphicsDevice graphics, SpriteBatch spriteBatch)
        {
            stateStack[stateStack.Count - 1].render(graphics, spriteBatch);
        }

        /**
         * Calls each state's loadContent() function to reload any
         * content. This should be called whenever XNA requests that
         * content should be reloaded through its LoadContent() function.
         */
        public void reloadContent()
        {
            for (int i = 0; i < stateStack.Count; i++)
                stateStack[i].loadContent();
        }


        #region state managment functions

        public void pushState(GameState state)
        {
            changes.Add(new ChangeInfo(state, changeOperation.PUSH));
        }

        public void popState()
        {
            changes.Add(new ChangeInfo(null, changeOperation.POP));
        }

        /**
         * Changes to the state stack must only occur before update and
         * render functions are called. This way state's foreground() and
         * background() functions will be called at the correct time.
         */
        private void doChanges()
        {
            if (changes.Count == 0)
                return;

            for (int i = 0, n = changes.Count; i < n; i++)
            {
                ChangeInfo change = changes[i];

                if (change.operation == changeOperation.PUSH)
                {
                    //if we're pushing on top of another state, alert it
                    if (stateStack.Count > 0)
                        stateStack[stateStack.Count - 1].background();
                    stateStack.Add(change.state);
                    change.state.foreground();
                }
                else //pop function
                {
                    if (stateStack.Count > 0)
                        stateStack.RemoveAt(stateStack.Count - 1);

                    if (stateStack.Count > 0)
                        stateStack[stateStack.Count - 1].foreground();
                    else
                        game.Exit();
                }
            }

            changes.Clear();
        }

        #endregion
    }
}
