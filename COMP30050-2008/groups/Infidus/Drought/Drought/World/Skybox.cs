using System;
using System.Collections.Generic;
using System.Text;
using Drought.Graphics;
using Microsoft.Xna.Framework.Content;
using Microsoft.Xna.Framework.Graphics;

namespace Drought.World
{
    class Skybox : Model3D
    {
        public Skybox(string modelName, Camera camera) :
            base(modelName)
        {
            position = camera.getPosition();
        }

        public override void loadContent(ContentManager content)
        {
            //load the model and the texture
        }

        public override void update(Microsoft.Xna.Framework.GameTime gametime)
        {
            
        }

        public override void render(GraphicsDevice graphics)
        {
            throw new Exception("The method or operation is not implemented.");
        }
    }
}
