using System;
using System.Collections.Generic;
using System.Text;
using Microsoft.Xna.Framework.Content;
using Microsoft.Xna.Framework.Graphics;

namespace Drought.Graphics 
{
    public enum modelType : int { XYZ, Truck, Car, Skybox };

    public class ModelLoader 
    {
        private static readonly int MODEL_COUNT = 4;

        private Model[] models = new Model[MODEL_COUNT];

        private Texture2D[][] textures = new Texture2D[MODEL_COUNT][];

        private Effect[] effects = new Effect[MODEL_COUNT];

        private bool[] isLoaded = new bool[MODEL_COUNT];

        private ContentManager content;

        private GraphicsDevice graphics;

        public ModelLoader(ContentManager contentManager, GraphicsDevice graphicsDevice)
        {
            content = contentManager;
            graphics = graphicsDevice;
            
            for (int i=0; i<effects.Length; i++) {
                effects[i] = contentManager.Load<Effect>("EffectFiles/model");
            }
        }

        public Model getModel(modelType model) {
            if (isLoaded[(int)model]) {
                return models[(int)model];
            }
            else {
                return loadModel(model);
            }
        }

        public Texture2D[] getModelTextures(modelType model)
        {
            if (isLoaded[(int)model]) {
                return textures[(int)model];
            }
            else {
                loadModel(model);
                return textures[(int)model];
            }
        }

        private Model loadModel(modelType model)
        {
            String modelString = "";

            switch (model) {
                case modelType.XYZ: modelString = "Models/xyz"; break;
                case modelType.Truck: modelString = "Models/Truck/truck"; break;
                case modelType.Car: modelString = "Models/Car/car"; break;
                case modelType.Skybox: modelString = "Models/Skybox/skybox"; break;
            }

            Model newModel = content.Load<Model>(modelString);
            models[(int)model] = newModel;

            int textureCount = 0;
            foreach (ModelMesh mesh in newModel.Meshes)
                textureCount += mesh.Effects.Count;

            Texture2D[] newTextures = new Texture2D[textureCount];

            int i = 0;
            foreach (ModelMesh mesh in newModel.Meshes)
                foreach (BasicEffect basicEffect in mesh.Effects)
                    newTextures[i++] = basicEffect.Texture;

            textures[(int)model] = newTextures;

            foreach (ModelMesh mesh in newModel.Meshes)
                foreach (ModelMeshPart meshPart in mesh.MeshParts)
                    meshPart.Effect = effects[(int)model].Clone(graphics);

            isLoaded[(int)model] = true;

            return newModel;
        }
    }
}
