using System;
using System.Collections.Generic;
using System.Text;
using Microsoft.Xna.Framework.Graphics;
using Microsoft.Xna.Framework.Content;
using Microsoft.Xna.Framework;
using Drought.World;

namespace Drought.Graphics
{
    public class Model3D
    {
        public Camera camera;

        private static Effect effect;

        private static GraphicsDevice graphics;

        string modelName;

        Model model;

        Texture2D[] textures;

        public Vector3 position;

        public Vector3 rotationAngles;

        public Vector3 scaleFactors;

        Matrix projectionMatrix;

        public Model3D(string modelName, Camera camera)
        {
            this.modelName = modelName;
            this.camera = camera;

            rotationAngles = new Vector3(0.0f);
            scaleFactors = new Vector3(1.0f);

            position = camera.getPosition(); 
            projectionMatrix = camera.getProjectionMatrix();
        }

        public void loadContent(ContentManager content, GraphicsDevice graphics)
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

        public void render(GraphicsDevice graphics)
        {
            int i = 0;
            foreach (ModelMesh mesh in model.Meshes)
            {
                foreach (Effect currentEffect in mesh.Effects)
                {
                    currentEffect.CurrentTechnique = effect.Techniques["Textured"];

                    Matrix worldMatrix = Matrix.CreateRotationX(rotationAngles.X) * Matrix.CreateRotationY(rotationAngles.Y) * Matrix.CreateRotationZ(rotationAngles.Z) *
                        Matrix.CreateScale(scaleFactors) * 
                        Matrix.CreateTranslation(position);

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
