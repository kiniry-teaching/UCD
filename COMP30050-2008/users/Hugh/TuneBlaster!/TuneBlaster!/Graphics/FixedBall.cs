using System;
using System.Collections.Generic;
using System.Text;
using Microsoft.Xna.Framework.Graphics;
using Microsoft.Xna.Framework;

namespace TuneBlaster_.Graphics
{
    class FixedBall : Image
    {
        #region Fields (core, colour, initialRoatation, coreDistance)

        Core core;
        value colour;
        float initialRotation, coreDistance;

        #endregion

        #region Main Methods(FixedBall, Initialise)

        public FixedBall(Core c, value v) 
        {
            core = c;
            colour = v;    
        }

        public override void Initialise()
        {
            base.Initialise();
            coreDistance = Vector2.Distance(Position, core.Position);
            rotation = core.Rotation;
            initialRotation = (float)(3*Math.PI/4 + Math.Acos((core.Position.X - Position.X) / coreDistance) + Math.Asin((core.Position.Y - Position.Y) / coreDistance));
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

        #endregion

    }
}
