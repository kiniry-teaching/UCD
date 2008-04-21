using Microsoft.Xna.Framework.Graphics;

namespace Drought.Graphics
{
    /** Wraps a Model and a Texture2D[] together for convenience. */
    struct Model3D
    {
        private Model model;
        public Model Model
        {
            get { return model; }
        }

        private Texture2D[] textures;
        public Texture2D[] Textures
        {
            get { return textures; }
        }

        private Effect effect;
        public Effect Effect
        {
            get { return effect; }
        }

        private float scale;
        public float Scale {
            get { return scale; } 
        }

        public Model3D(Model aModel, Texture2D[] someTextures, Effect anEffect, float aScale)
        {
            model = aModel;
            textures = someTextures;
            effect = anEffect;
            scale = aScale;
        }
    }
}
