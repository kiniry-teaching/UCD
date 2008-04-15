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

        private Texture2D[] modelTextures;
        public Texture2D[] ModelTextures
        {
            get { return modelTextures; }
        }

        private Effect modelEffect;
        public Effect ModelEffect
        {
            get { return modelEffect; }
        }

        public Model3D(Model aModel, Texture2D[] someTextures, Effect anEffect)
        {
            model = aModel;
            modelTextures = someTextures;
            modelEffect = anEffect;
        }
    }
}
