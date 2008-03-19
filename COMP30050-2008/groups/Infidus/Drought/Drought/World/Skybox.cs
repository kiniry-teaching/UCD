using System;
using System.Collections.Generic;
using System.Text;
using Drought.Graphics;
using Microsoft.Xna.Framework.Content;
using Microsoft.Xna.Framework.Graphics;
using Microsoft.Xna.Framework;

namespace Drought.World
{
    class Skybox
    {
        Model model;

        public Skybox(Camera camera, Model model)
        {
//            model.rotationAngles += new Vector3(MathHelper.PiOver2, 0, 0);
//            model.scaleFactors += new Vector3(50, 50, 50);
        }

        public void update(GameTime gametime)
        {
 //           model.position = model.camera.getPosition();
        }

        public void render(GraphicsDevice graphics)
        {
 //           model.render(graphics);
        }
    }
}
