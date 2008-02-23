using System;
using System.Collections.Generic;
using System.Text;
using Microsoft.Xna.Framework.Graphics;
using Microsoft.Xna.Framework;

namespace TuneBlaster_.Graphics
{
    class FixedBall : Image
    {
        Core core;
        value colour;
        float initialRotation, coreDistance;

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
            initialRotation = core.Rotation;
        }

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

    }
}
