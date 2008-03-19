using System;
using System.Collections.Generic;
using System.Text;
using Microsoft.Xna.Framework;
using Microsoft.Xna.Framework.Graphics;
using Microsoft.Xna.Framework.GamerServices;
using Drought.State;

namespace Drought.GameStates {

    class SignInState : GameState {

        private delegate void Sort(int[] items);

        /**
         * If a profile is set to sign in automatically, it isn't recognised for 
         * a few milliseconds after starting the game; waiting 10 game updates
         * before checking gives the game a chance to detect the player.
         */
        public static readonly int WAIT_FOR_AUTOSIGNIN = 10;

        /** How many game updates this SignInState has waited. */
        private int waited;

        public SignInState(IStateManager manager, Game game, bool wait) : base(manager, game) {
            waited = wait ? 0 : 10;
        }

        public override void loadContent() {}

        public override void background() {}

        public override void foreground() {}

        public override void update(GameTime gameTime) {
            if (Gamer.SignedInGamers.Count > 0) {
                getStateManager().popState();
            }
            else if (waited == WAIT_FOR_AUTOSIGNIN && !Guide.IsVisible) {
                Guide.ShowSignIn(1, false);
            }
            else {
                waited++;
            }
        }

        public override void render(GraphicsDevice graphics, SpriteBatch spriteBatch) {}
    }
}
