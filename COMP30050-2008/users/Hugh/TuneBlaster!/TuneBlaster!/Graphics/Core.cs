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
        GamePadState gamePadState;

        #endregion

        #region Main Methods (Core, Initialise, Draw, Update)

        public Core(GamePadState g)
        {
            balls = new List<FixedBall>();
            gamePadState = g;
        }

        public override void Initialise()
        {
            base.Initialise();
            Position = new Vector2(400, 400);
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

        public void Update(GameTime gameTime, KeyboardState keyBoardState)
        {
            Move(keyBoardState);
        }

        #endregion

        #region Action Methods (SetRotation, Move, AddBall, RemoveBall)

        public void SetRotation()
        {
            oldRotation = rotation;
            if (gamePadState.ThumbSticks.Left.X > 0)
            {
                acceleration += 0.1f;
            }
            if (acceleration > 1.0)
            {
                acceleration = 1.0f;
            }

            else if (gamePadState.ThumbSticks.Left.X < 0)
            {
                acceleration -= 0.1f;
            }
            if (acceleration > 1.0)
            {
                acceleration = 1.0f;
            }
        }

        public void Move(KeyboardState keyBoardState)
        {
            //SetRotation(gamepadState);
            oldRotation = rotation;
            SetKeyboardRotation(keyBoardState);
            for (int i = 0; i < balls.Count; i++) 
            {
                balls[i].Move(rotation-oldRotation);
            }           
        }

        public void addBall(FixedBall f)
        {
            balls.Add(f);
            ballsSize++;
            Console.WriteLine(ballsSize);
        }

        public void removeBall(FixedBall f)
        {
            for (int i = 0; i < ballsSize; i++)
            {
                if (balls[i].Equals(f))
                {
                    balls.Remove(balls[i]);
                }
            }
        }

        #endregion

        #region Input Methods (SetControllerRotation, SetKeyBoardRotation)

        public void SetControllerRotation()
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
                acceleration = 0.05f;
            }
            if (keyBoardState.IsKeyDown(Keys.Left))
            {
                acceleration = -0.05f;
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
