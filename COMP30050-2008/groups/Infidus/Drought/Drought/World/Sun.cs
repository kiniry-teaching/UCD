using System;
using System.Collections.Generic;
using System.Text;
using Microsoft.Xna.Framework;

namespace Drought.World
{
    public class Sun
    {
        //TODO add ambient lighting.....

        private Vector3 position;
        private float power;

        private int step;
        private double oldTime;

        private bool enabled;

        public bool isEnabled
        {
            get { return enabled; }
            set { enabled = value; }
        }

        public Sun(Vector3 position)
        {
            this.position = position;

            power   = 1;
            step    = 100;
            oldTime = 0;

            enabled = false;
        }

        public Vector3 getPosition()
        {
            return position;
        }

        public float getPower()
        {
            return power;
        }

        public void setPosition(Vector3 position)
        {
            this.position = position;
        }

        public void setPower(float power)
        {
            this.power = power;
        }

        /**
         * Sun Moves in circle around the x=0 line or "the origin in the yz plane".
         * 
         */
        public void update(GameTime gameTime)
        {
            if (enabled)
                if (gameTime.TotalGameTime.TotalMilliseconds - oldTime > step / 2)
                {
                    Vector3 normal = new Vector3(0, position.Z, -position.Y);
                    normal.Normalize();
                    position += normal;

                    //Power scaling. Power is clamped to 0  below the vertical and 1 above 30 degrees to the vertical. 
                    //Power  is lerped between 0 and 30 degrees. 
                    float limit = position.Length() * (float)Math.Sin(MathHelper.Pi / 6);
                    power = MathHelper.Clamp(position.Z / limit, 0, 1);

                    //Console.WriteLine("position: {2}\nangle: {0}\npower: {1}\n\n", MathHelper.ToDegrees((float)Math.Asin(position.Z / position.Length())), power, position);

                    oldTime = gameTime.TotalGameTime.TotalMilliseconds;
                }
        }
    }
}
