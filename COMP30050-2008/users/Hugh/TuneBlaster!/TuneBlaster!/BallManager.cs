using System;
using System.Collections.Generic;
using System.Text;
using System.Text;
using Microsoft.Xna.Framework.Graphics;
using Microsoft.Xna.Framework;
using TuneBlaster_.Graphics;

namespace TuneBlaster_
{
    class BallManager
    {
        MovingBall ball;
        Random generator;
        Core core;
        SpriteBatch s;
        Texture2D t;

        public BallManager(Core c)
        {
            core = c;
        }

        public void Initialise()
        {
            ball = new MovingBall(core,Image.value.green);
            ball.Initialise(new Vector2(50f, 50f), new Vector2(0f, 0f));
        }

        public void LoadGraphicsContent(SpriteBatch spriteBatch, Texture2D texture)
        {
            ball.LoadGraphicsContent(spriteBatch, texture);
            s = spriteBatch;
            t = texture;
        }

        public void Update(GameTime gameTime)
        {
            if (ball.IsLive())
            {
                ball.Move();
                //ball.Update(gameTime);
            }
            else
            {
                Initialise();
                ball.LoadGraphicsContent(s, t);
            }
        }

        public void Draw(GameTime gameTime)
        {
            ball.Draw(gameTime);
        }
    }
}
