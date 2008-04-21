using System;
using System.Collections.Generic;
using System.Text;
using Microsoft.Xna.Framework.Content;
using Microsoft.Xna.Framework.Graphics;
using Microsoft.Xna.Framework;
using Drought.Graphics;

namespace Drought.World
{
    class Skybox
    {
        private Camera camera;

        private Sun sun;

        private Model3D model;

        public Skybox(Camera camera, Sun sun, Model3D model)
        {
            this.camera = camera;
            this.sun = sun;
            this.model = model;
        }

        public void render()
        {
            Matrix[] transforms = new Matrix[model.Model.Bones.Count];
            model.Model.CopyAbsoluteBoneTransformsTo(transforms);

            Matrix worldMatrix = Matrix.CreateScale(model.Scale) * Matrix.CreateRotationX(MathHelper.PiOver2) * Matrix.CreateTranslation(camera.getPosition() + new Vector3(0,0,50)); 

            int i = 0;
            foreach (ModelMesh mesh in model.Model.Meshes)
            {
                foreach (Effect currentEffect in mesh.Effects)
                {
                    currentEffect.CurrentTechnique = model.Effect.Techniques["Textured"];

                    currentEffect.Parameters["xWorldViewProjection"].SetValue(transforms[mesh.ParentBone.Index] * worldMatrix * camera.getViewMatrix() * camera.getProjectionMatrix());
                    currentEffect.Parameters["xWorld"].SetValue(worldMatrix);
                    currentEffect.Parameters["xTexture"].SetValue(model.Textures[i++]);
                    currentEffect.Parameters["xEnableLighting"].SetValue(false);
                    currentEffect.Parameters["xLightPosition"].SetValue(camera.getPosition() + sun.getPosition()); //???
                    currentEffect.Parameters["xLightPower"].SetValue(sun.getPower());
                }
                mesh.Draw();
            }
        }
    }
}
