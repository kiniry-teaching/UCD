using System;
using Microsoft.Xna.Framework.Content;
using Microsoft.Xna.Framework.Graphics;

namespace Drought.Graphics 
{
    public enum modelType : int { XYZ, Truck, Car, Tank, Skybox };

    class ModelLoader 
    {
        private static readonly int MODEL_COUNT = 5;

        private Model3D[] models = new Model3D[MODEL_COUNT];

        private Effect modelEffect;

        private bool[] isLoaded = new bool[MODEL_COUNT];

        private ContentManager content;

        private GraphicsDevice graphics;

        public ModelLoader(ContentManager contentManager, GraphicsDevice graphicsDevice)
        {
            content = contentManager;
            graphics = graphicsDevice;
            
            modelEffect = contentManager.Load<Effect>("EffectFiles/model");
        }

        public Model3D getModel3D(modelType model)
        {
            if (isLoaded[(int)model]) {
                return models[(int)model];
            }
            else {
                return loadModel(model);
            }
        }
        
        private Model3D loadModel(modelType model)
        {
            String modelString = "";
            float modelScale = 1.0f;

            switch (model) {
                case modelType.XYZ: modelString = "Models/xyz"; modelScale = 1.0f; break;
                case modelType.Truck: modelString = "Models/Truck/newtruck"; modelScale = 0.005f; break;
                case modelType.Car: modelString = "Models/Car/car"; modelScale = 0.75f; break;
                case modelType.Tank: modelString = "Models/Tank/tank"; modelScale = 0.005f; break;
                case modelType.Skybox: modelString = "Models/Skysphere/skysphere2"; modelScale = 10.0f; break;
            }

            Model newModel = content.Load<Model>(modelString);

            int textureCount = 0;
            foreach (ModelMesh mesh in newModel.Meshes)
                textureCount += mesh.Effects.Count;

            Texture2D[] newTextures = new Texture2D[textureCount];

            int i = 0;
            foreach (ModelMesh mesh in newModel.Meshes)
                foreach (BasicEffect basicEffect in mesh.Effects)
                    newTextures[i++] = basicEffect.Texture;

            foreach (ModelMesh mesh in newModel.Meshes)
                foreach (ModelMeshPart meshPart in mesh.MeshParts)
                    meshPart.Effect = modelEffect.Clone(graphics);

            isLoaded[(int)model] = true;

            models[(int)model] = new Model3D(newModel, newTextures, modelEffect, modelScale);

            return models[(int)model];
        }
    }
}
