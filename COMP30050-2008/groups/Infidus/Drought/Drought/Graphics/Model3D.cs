using System;
using System.Collections.Generic;
using System.Collections;
using System.Text;
using Microsoft.Xna.Framework.Graphics;
using Microsoft.Xna.Framework.Content;
using Microsoft.Xna.Framework;
using Drought.World;

namespace Drought.Graphics
{
    public class Model3D
    {
        private static Dictionary<string,Model3D> instances = new Dictionary<string,Model3D>();

        private static Camera camera;

        private static Effect effect;

        private static GraphicsDevice graphics;

        private string modelName;

        private Model model;

        private Texture2D[] textures;

        private Matrix projectionMatrix;

        private Model3D(string modelName, Camera camera, ContentManager content, GraphicsDevice graphics)
        {
            this.modelName = modelName;
            this.camera = camera;

            projectionMatrix = camera.getProjectionMatrix();

            loadContent(content, graphics);
        }

        public Model3D getInstance(string model, Camera camera)
        {

        }

        private void loadContent(ContentManager content, GraphicsDevice graphics)
        {
            if (effect == null)
                effect = content.Load<Effect> ("EffectFiles/model");

            model = content.Load<Model>(modelName);

            int textureCount = 0;
            foreach (ModelMesh mesh in model.Meshes)
                textureCount += mesh.Effects.Count;
                    
            textures = new Texture2D[textureCount];

            int i = 0;
            foreach (ModelMesh mesh in model.Meshes)
                foreach (BasicEffect basicEffect in mesh.Effects)
                    textures[i++] = basicEffect.Texture;

            foreach (ModelMesh mesh in model.Meshes)
                foreach (ModelMeshPart meshPart in mesh.MeshParts)
                    meshPart.Effect = effect.Clone(graphics);
        }

        public void render(GraphicsDevice graphics, Matrix orientation, Vector3 position, Vector2 scaleFactors)
        {
            Matrix worldMatrix = orientation * Matrix.CreateTranslation(position) * Matrix.CreateScale(scaleFactors);

            int i = 0;
            foreach (ModelMesh mesh in model.Meshes)
            {
                foreach (Effect currentEffect in mesh.Effects)
                {
                    currentEffect.CurrentTechnique = effect.Techniques["Textured"];

                    currentEffect.Parameters["xWorld"].SetValue(worldMatrix);
                    currentEffect.Parameters["xView"].SetValue(camera.getViewMatrix());
                    currentEffect.Parameters["xProjection"].SetValue(projectionMatrix);
                    currentEffect.Parameters["xTexture"].SetValue(textures[i++]);
                }
                mesh.Draw();
            }

        }

    }
}
