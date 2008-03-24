using System;
using System.Collections.Generic;
using System.Text;
using Microsoft.Xna.Framework.Content;
using Microsoft.Xna.Framework.Graphics;
using Microsoft.Xna.Framework;

namespace Drought.World
{
    class Skybox
    {
        Camera camera;
        Effect effect;
        Model model;
        Texture2D[] modelTextures;

        public Skybox(Camera camera)
        {
            this.camera = camera;
        }

        public void loadContent(ContentManager content, GraphicsDevice graphics)
        {
            model = content.Load<Model>("Models/Skydome/dome");
            effect = content.Load<Effect>("EffectFiles/model");

            int textureCount = 0;
            foreach (ModelMesh mesh in model.Meshes)
                textureCount += mesh.Effects.Count;

            modelTextures = new Texture2D[textureCount];

            int i = 0;
            foreach (ModelMesh mesh in model.Meshes)
                foreach (BasicEffect basicEffect in mesh.Effects)
                    modelTextures[i++] = basicEffect.Texture;

            foreach (ModelMesh mesh in model.Meshes)
                foreach (ModelMeshPart meshPart in mesh.MeshParts)
                    meshPart.Effect = effect.Clone(graphics);
        }

        public void render()
        {
            Matrix[] transforms = new Matrix[model.Bones.Count];
            model.CopyAbsoluteBoneTransformsTo(transforms);

            Matrix worldMatrix = Matrix.CreateScale(5000, 5000, 5000) * Matrix.CreateTranslation(camera.getPosition() - new Vector3(0, 0, 1000));

            int i = 0;
            foreach (ModelMesh mesh in model.Meshes)
            {
                foreach (Effect currentEffect in mesh.Effects)
                {
                    currentEffect.CurrentTechnique = effect.Techniques["Textured"];

                    currentEffect.Parameters["xWorldViewProjection"].SetValue(transforms[mesh.ParentBone.Index] * worldMatrix * camera.getViewMatrix() * camera.getProjectionMatrix());
                    currentEffect.Parameters["xWorld"].SetValue(worldMatrix);
                    currentEffect.Parameters["xTexture"].SetValue(modelTextures[i++]);

                    //HLSL testing
                    currentEffect.Parameters["xEnableLighting"].SetValue(false);
                    currentEffect.Parameters["xLightPosition"].SetValue(new Vector3(0, 0, 200));
                    currentEffect.Parameters["xLightPower"].SetValue(1);

                }
                mesh.Draw();
            }
        }
    }
}
