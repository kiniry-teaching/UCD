using System;
using System.Collections.Generic;
using System.Text;
using Microsoft.Xna.Framework.Input;
using Microsoft.Xna.Framework.Graphics;
using Microsoft.Xna.Framework.Storage;
using Microsoft.Xna.Framework;

namespace TuneBlaster_.Graphics
{
    class Core : Image
    {
        #region Fields (ballsSize, oldRotation, acceleration, balls, maxAcceleration)

        int ballsSize;
        float oldRotation;
        public float acceleration;
        public List<FixedBall> balls;
        static float maxAcceleration = 0.05f;

        #endregion

        #region Main Methods (Core, Initialise, Draw, Update)

        public Core()
        {
            balls = new List<FixedBall>();
        }

        public override void Initialise(Vector2 mySize, Vector2 myPosition, Game g)
        {
            base.Initialise(mySize, myPosition, g);
            acceleration = 0f;
            oldRotation = 0f;
        }

        public override void Draw(GameTime gameTime)
        {
            base.Draw(gameTime);
            for (int i = 0; i < balls.Count; i++) 
            {
                balls[i].Draw(gameTime);
            }
        }

        public void Update(GameTime gameTime, KeyboardState keyBoardState, GamePadState gamePadState)
        {
            Move(keyBoardState, gamePadState);
            for (int i = 0; i < balls.Count; i++)
            {
                if (balls[i].IsDead())
                {
                    balls.Remove(balls[i]);
                }
            }
        }

        #endregion

        #region Action Methods (Move, AddBall, RemoveBall)


        public void Move(KeyboardState keyBoardState, GamePadState gamePadState)
        {
            oldRotation = rotation;
            SetKeyboardRotation(keyBoardState);
            SetControllerRotation(gamePadState);
            for (int i = 0; i < balls.Count; i++) 
            {
                balls[i].Move(rotation-oldRotation);
            }           
        }

        public void addBall(FixedBall f)
        {
            balls.Add(f);
            ballsSize++;
            CheckExplosions();
        }

        public void CheckExplosions()
        {
            if (ballsSize > 4)
            {
                for (int i = 0; i < ballsSize; i++)
                {
                    balls[i].Destroy();
                }
                ballsSize = 0;
            }
        }


        #endregion

        #region Input Methods (SetControllerRotation, SetKeyBoardRotation)

        public void SetControllerRotation(GamePadState gamePadState)
        {
            if (gamePadState.ThumbSticks.Left.X < 0.0f)
            {
                acceleration += 0.01f * gamePadState.Triggers.Right;
                acceleration *= 0.9f;

                if (acceleration >= maxAcceleration)
                {
                    acceleration = maxAcceleration;
                }
            }
            else if (gamePadState.ThumbSticks.Left.X > 0.0f)
            {
                acceleration -= 0.01f * gamePadState.Triggers.Right;
                acceleration *= 0.9f;

                if (acceleration <= -maxAcceleration)
                {
                    acceleration = -maxAcceleration;
                }
            }
            else
            {
                acceleration *= 0.9f;
            }

            rotation += acceleration;
        }

        public void SetKeyboardRotation(KeyboardState keyBoardState)
        {
            if (keyBoardState.IsKeyDown(Keys.Right))
            {
                if (keyBoardState.IsKeyDown(Keys.Left))
                {
                    acceleration *= 0.90f;
                }
                acceleration = 0.03f;
            }
            if (keyBoardState.IsKeyDown(Keys.Left))
            {
                acceleration = -0.03f;
            }
            else
            {
                acceleration *= 0.9f;
            }

            rotation += acceleration;

        }

#endregion

        #region Getter/Setter Methods (getBallSize)

        public int getBallSize()
        {
            return ballsSize;
        }

        #endregion

    }
}
