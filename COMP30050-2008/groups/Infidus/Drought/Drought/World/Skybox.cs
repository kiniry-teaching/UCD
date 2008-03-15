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
        Model3D model;

        public Skybox(Camera camera)
        {
            model = new Model3D("Models/Skybox/skybox", camera);
        }

        public void loadContent(ContentManager content, GraphicsDevice graphics)
        {
            model.loadContent(content, graphics);
        }

        public void setScale(Vector3 scaleFactors)
        {
            model.scaleFactors = scaleFactors;
        }

        public void update(GameTime gametime)
        {
            model.position = model.camera.getPosition();
        }

        public void render(GraphicsDevice graphics)
        {
            model.render(graphics);
        }
    }
}
