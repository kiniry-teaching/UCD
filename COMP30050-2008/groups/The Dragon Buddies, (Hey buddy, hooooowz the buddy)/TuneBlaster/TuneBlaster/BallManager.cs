using System;
using System.Collections.Generic;
using System.Text;
using Microsoft.Xna.Framework.Graphics;
using Microsoft.Xna.Framework;
using TuneBlaster_.Graphics;

namespace TuneBlaster_
{
    /// <summary>
    /// The class in charge of creating all the balls in the regular game mode
    /// Author Hugh Corrigan, Ahmed Warreth, Dermot Kirby
    /// </summary>
    class BallManager
    {
        #region Fields (ball, generator, core, spritebatch, texture)

        MovingBall ball;
        Random generator;
        Core core;
        SpriteBatch s;
        Texture2D green, red, purple, blue;
        Game game;
        Image.value colour;

        #endregion

        #region Main Methods (BallManager, Initialise, LoadGraphicsContent, Update, Draw)

        /*
         * Constructor
         * */
        public BallManager(Core c, Game g)
        {
            core = c;
            game = g;
            generator = new Random();
        }

        /*
         * Initialise the ball(s)
         * */
        public void Initialise()
        {
            ResetColour();
            ball = new MovingBall(core, colour);
            Console.WriteLine("new ball");
            ball.Initialise(new Vector2(50f, 50f), StartPosition(), game);
        }

        /*
         * Generate a valid spawning point for the ball
         * */
        public Vector2 StartPosition()
        {
            int temp = generator.Next(1);
            Vector2 startPosition = Vector2.One;
            if (temp == 0)
            {
                temp = generator.Next(2);
                int tempy = generator.Next(721);
                if (temp == 1)
                    temp = 801;
                startPosition = new Vector2(temp,tempy);
            }

            else
            {
                temp = generator.Next(2);
                int tempx = generator.Next(801);
                if (temp == 2)
                    temp = 801;
                startPosition = new Vector2(tempx, temp);
            }

            return startPosition;
        }

        /*
         * Load in all possible graphics
         * */
        public void LoadGraphicsContent(SpriteBatch spriteBatch)
        {
            green = game.Content.Load<Texture2D>(@"Resources\Textures\Green");
            blue = game.Content.Load<Texture2D>(@"Resources\Textures\Blue");
            purple = game.Content.Load<Texture2D>(@"Resources\Textures\Pur");
            red = game.Content.Load<Texture2D>(@"Resources\Textures\Red");
            s = spriteBatch;
            LoadBallGraphicsContent();
        }

        /*
         * Load the correct texture depending on the ball's colour
         * */
        public void LoadBallGraphicsContent()
        {
            if (ball.colour == Image.value.green)
            {
                ball.LoadGraphicsContent(s,green);
            }

            else if (ball.colour == Image.value.red)
            {
                ball.LoadGraphicsContent(s, red);
            }

            else if (ball.colour == Image.value.purple)
            {
                ball.LoadGraphicsContent(s, purple);
            }

            else if (ball.colour == Image.value.blue)
            {
                ball.LoadGraphicsContent(s, blue);
            }

        }
        
        /*
         * Randomly select a colour for the ball to be
         * */
        public void ResetColour()
        {
            int temp = generator.Next(4);
            if (temp == 0)
            {
                colour = Image.value.green;
            }

            else if (temp == 1)
            {
                colour = Image.value.purple;
            }

            else if (temp == 2)
            {
                colour = Image.value.blue;
            }

            else if (temp == 3)
            {
                colour = Image.value.red;
            }
        }

        /*
         * Update the ball, and generate new ones if necessary
         * */
        public void Update(GameTime gameTime)
        {
            if (ball.IsLive())
            {
                ball.Move();
            }
            else
            {
                Initialise();
                LoadBallGraphicsContent();
            }
        }

        /*
         * Draw the ball(s) 
         * */
        public void Draw(GameTime gameTime)
        {
            ball.Draw(gameTime);
        }

        #endregion
    }
}
