using System;
using System.Collections.Generic;
using System.Text;
using Microsoft.Xna.Framework.Graphics;
using Microsoft.Xna.Framework;

namespace TuneBlaster_.Graphics
{
    /// <summary>
    /// The class for the balls that have become stationary due to a colission
    /// Author Hugh Corrigan
    /// </summary>
    class FixedBall : Image
    {
        #region Fields (core, colour, initialRoatation, coreDistance)

        Core core;
        value colour;
        float initialRotation, coreDistance;
        bool dead, locked;

        #endregion

        #region Main Methods(FixedBall, Initialise)

        public FixedBall(Core c, value v) 
        {
            core = c;
            colour = v;    
        }

        public override void Initialise(Game g)
        {
            locked = true;
            dead = false;
            base.Initialise(g);
            coreDistance = Vector2.Distance(Position, core.Position);
            //rotation = core.Rotation;
            if (((core.Position.X - Position.X) / coreDistance) > Math.PI)
            {
                initialRotation = (float) Math.Sin((core.Position.Y - Position.Y + 0.53*origin.Y ) / coreDistance);
            }
            else
            {
                initialRotation = (float) (Math.PI + Math.Sin((core.Position.Y - Position.Y + 0.53*origin.Y) / coreDistance));
            }
            // initialRotation = (float)(Math.Sin((core.Position.X - Position.X) / coreDistance) + Math.Sin((core.Position.Y - Position.Y) / coreDistance));
        }

        #endregion

        #region Action Methods (GetRotation, Move)

        public void GetRotation(float rotate)
        {
            rotation += rotate;
            initialRotation += rotate;

            Position = core.Position + new Vector2((float)(coreDistance * Math.Cos(initialRotation)), (float) (coreDistance * Math.Sin(initialRotation)));
        }

        public void Move(float rotate)
        {
            GetRotation(rotate);
        }

        public void Destroy()
        {
            dead = true;
        }

        public bool IsDead()
        {
            return dead;
        }

        public void Unlock()
        {
            locked = false;
        }

        #endregion

    }
}
