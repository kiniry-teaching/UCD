using System;
using System.Collections.Generic;
using System.Text;
using TuneBlaster_.Graphics;
using Microsoft.Xna.Framework.Graphics;
using Microsoft.Xna.Framework;

namespace TuneBlaster_
{
    class BallGenerator
    {
        LinkedList<MovingBall> balls;
        Random generator;
        Core core;
        SpriteBatch spritebatch;
        Texture2D texture;
        Texture2D green, red, purple, blue;
        Game game;
        

        public BallGenerator(Core c, SpriteBatch s, Texture2D t, Game g)
        {
            balls = new LinkedList<MovingBall>();
            generator = new Random();
            core = c;
            spritebatch = s;
            texture = t;
            game = g;
        }

        public void Initialise()
        {
            green = game.Content.Load<Texture2D>(@"Resources\Textures\Green");
            blue = game.Content.Load<Texture2D>(@"Resources\Textures\Blue");
            purple = game.Content.Load<Texture2D>(@"Resources\Textures\Pur");
            red = game.Content.Load<Texture2D>(@"Resources\Textures\Red");

            for (int i = 0; i < 10; i++)
            {
                balls.AddLast(new MovingBall(core, ResetColour()));
            }

            balls.First.Value.Initialise(new Vector2(50f, 50f), new Vector2(1140f, 600f),game);

            
            LinkedListNode<MovingBall> temp = balls.First.Next;

            while (temp.Next != null)
            {
                temp.Value.Initialise(new Vector2(50f, 50f), temp.Previous.Value.Position - new Vector2(0f, 50f), game);
                temp = temp.Next;
            }
            temp.Value.Initialise(new Vector2(50f, 50f), temp.Previous.Value.Position - new Vector2(0f, 50f), game);
        }

        public void LoadGraphicsContent()
        {
            LinkedListNode<MovingBall> temp = balls.First;

            while (temp.Next != null)
            {
                LoadBallGraphicsContent(temp.Value);
                temp = temp.Next;
            }
            LoadBallGraphicsContent(temp.Value);
        }

        /*
         * Load the correct texture depending on the ball's colour
         * */
        public void LoadBallGraphicsContent(MovingBall ball)
        {
            if (ball.colour == Image.value.green)
            {
                ball.LoadGraphicsContent(spritebatch, green);
            }

            else if (ball.colour == Image.value.red)
            {
                ball.LoadGraphicsContent(spritebatch, red);
            }

            else if (ball.colour == Image.value.purple)
            {
                ball.LoadGraphicsContent(spritebatch, purple);
            }

            else //if (ball.colour == Image.value.blue)
            {
                ball.LoadGraphicsContent(spritebatch, blue);
            }

        }

        /*
         * Randomly select a colour for the ball to be
         * */
        public Image.value ResetColour()
        {
            int temp = generator.Next(4);
            if (temp == 0)
            {
                return Image.value.green;
            }

            else if (temp == 1)
            {
                return Image.value.purple;
            }

            else if (temp == 2)
            {
                return Image.value.blue;
            }

            else
            {
                return Image.value.red;
            }
        }

        public MovingBall Remove()
        {
            MovingBall removed = balls.First.Value;

            balls.RemoveFirst();

            MovingBall temp = new MovingBall(core, ResetColour());
            balls.AddLast(temp);
            balls.Last.Value.Initialise(new Vector2(50f, 50f), balls.Last.Previous.Value.Position - new Vector2(0f, 50f), game);
            LoadBallGraphicsContent(balls.Last.Value);

            return removed;
        }

        public void Draw(GameTime gameTime)
        {
            LinkedListNode<MovingBall> temp = balls.First.Next;

            while (temp.Next != null)
            {
                temp.Value.Draw(gameTime);
                temp = temp.Next;
            }
            temp.Value.Draw(gameTime);
        }

    }
}
