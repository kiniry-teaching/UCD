using System;
using System.Collections.Generic;
using System.Text;
using Microsoft.Xna.Framework.Graphics;
using Microsoft.Xna.Framework.Content;
using Microsoft.Xna.Framework;

namespace Drought.Graphics
{
    abstract class Model3D
    {
        protected string modelName;

        protected Model3D model;

        protected Texture2D[] textures;

        protected Vector3 position;

        protected Vector3 rotation;

        public Model3D(string modelName)
        {
            this.modelName = modelName;
        }

        public abstract void loadContent(ContentManager content);

        public abstract void update(GameTime gametime);

        public abstract void render(GraphicsDevice graphics);

    }
}
