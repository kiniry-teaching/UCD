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
        int ballsSize;
        float oldRotation;
        public float acceleration;
        public List<FixedBall> balls;
        

        public Core()
        {
            balls = new List<FixedBall>();
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

        public void SetRotation(GamePadState gamepadState)
        {
            oldRotation = rotation;
            if (gamepadState.ThumbSticks.Left.X > 0)
            {
                acceleration += 0.1f;
            }
            if (acceleration > 1.0)
            {
                acceleration = 1.0f;
            }

            else if (gamepadState.ThumbSticks.Left.X < 0)
            {
                acceleration -= 0.1f;
            }
            if (acceleration > 1.0)
            {
                acceleration = 1.0f;
            }
        }

        public void SetKeyboardRotation(KeyboardState keyBoardState)
        {
            if (keyBoardState.IsKeyDown(Keys.Right))
            {
                if (keyBoardState.IsKeyDown(Keys.Left))
                {
                    acceleration *= 0.90f;
                }
                acceleration = 0.1f;
            }
            if (keyBoardState.IsKeyDown(Keys.Left))
            {
                acceleration = -0.1f;
            }
            else
            {
                acceleration *= 0.9f;
            }

            rotation += acceleration;

        }

        public void Move(GamePadState gamepadState, KeyboardState keyBoardState)
        {
            //SetRotation(gamepadState);
            oldRotation = rotation;
            SetKeyboardRotation(keyBoardState);
            for (int i = 0; i < balls.Count; i++) 
            {
                balls[i].Move(rotation-oldRotation);
            }           
        }

        public void Update(GameTime gameTime, GamePadState gamepadState,KeyboardState keyBoardState)
        {
            Move(gamepadState, keyBoardState);
        }

        public void addBall(FixedBall f)
        {
            balls.Add(f);
            ballsSize++;    
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

        public int getBallSize()
        {
            return ballsSize;
        }

    }
}
