using System;
using System.Collections.Generic;
using System.Text;
using Microsoft.Xna.Framework.Graphics;
using Microsoft.Xna.Framework;

namespace TuneBlaster_.Graphics
{
    /// <summary>
    /// The class for all balls that are not stationary, that gravitate towards the core
    /// Author Hugh Corrigan
    /// </summary>
    class MovingBall : Image
    {    
        #region Fields (core, live, angles, colour)

        Core core;
        bool live;
        float hypotenuse, x, y;
        value colour;

        #endregion

        #region Main Methods (MovingBall, Initialise)

        public MovingBall(Core c, value v)
        {
            core = c;
            colour = v;
        }

        public override void Initialise(Game g)
        {
            base.Initialise(g);
            live = true;
        }

        #endregion

        #region Return Methods (IsLive)

        public bool IsLive()
        {
            return live;
        }

        #endregion

        #region Action Methods (Collide, Move)

        public bool Collide()
        {
            if (Collide(core)) {
                return true;
            }

            for (int i = 0; i < core.getBallSize(); i++) 
            {
                //Console.WriteLine(Vector2.Distance(Position - origin + size / 2, core.balls[i].Position - core.balls[i].Origin + core.balls[i].Size / 2));
                if (Collide(core.balls[i])) 
                {
                    return true;
                }
            }
            return false;
        }

        public virtual void Move()
        {
            if (!Collide())
            {
                hypotenuse = Vector2.Distance(this.Position, core.Position);
                x = core.Position.X - this.Position.X;
                y = core.Position.Y - this.Position.Y;

                Position = new Vector2(2 * (x / hypotenuse) + Position.X, 2 * (y / hypotenuse) + Position.Y);
                //move with gravity
            }
            else
            {
                FixedBall f = new FixedBall(core, colour);
                f.Initialise(size, Position, game);
                f.LoadGraphicsContent(spriteBatch, texture);
                core.addBall(f);
                live = false;         
            }
        }

        #endregion
    }
}
