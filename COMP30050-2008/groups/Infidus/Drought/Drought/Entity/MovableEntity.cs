using System;
using System.Collections.Generic;
using System.Text;
using Microsoft.Xna.Framework;
using Drought.World;
using Microsoft.Xna.Framework.Graphics;
using Microsoft.Xna.Framework.Content;

namespace Drought.Entity
{

    class MovableEntity
    {
        private Vector3 position;

        private float velocity;

        private Vector3 heading;

        private NormalMap normalMap;

        private HeightMap heightMap;

        private Path path;

        private Model model;

        public MovableEntity(NormalMap normalMap, HeightMap heightMap)
        {
            path = new Path(new List<Vector3>());
            position = new Vector3(0, 0, 0);
            heading = new Vector3(0, 0, 0);
            velocity = 0.5f;
            this.normalMap = normalMap;
            this.heightMap = heightMap;
        }

        public void loadContent(ContentManager content)
        {
            model = content.Load<Model>("models/asdasd");
        }

        public void move()
        {
            if (!path.isFinished())
            {
                path.addDistance(velocity);
                position = path.getPosition();
            }
        }

        public void setPath(Path path)
        {
            this.path = path;
        }

        public void update()
        {
            move();
        }

        public void render(GraphicsDevice graphics)
        {
            // Set the position of the model in world space, and set the rotation.
            Vector3 modelPosition = Vector3.Zero;
            float modelRotation = 0.0f;

            // Set the position of the camera in world space, for our view matrix.
            Vector3 cameraPosition = new Vector3(0.0f, 50.0f, 5000.0f);

            graphics.Clear(Color.CornflowerBlue);

            // Copy any parent transforms.
            Matrix[] transforms = new Matrix[model.Bones.Count];
            model.CopyAbsoluteBoneTransformsTo(transforms);

            // Draw the model. A model can have multiple meshes, so loop.
            foreach (ModelMesh mesh in model.Meshes)
            {
                // This is where the mesh orientation is set, as well as our camera and projection.
                foreach (BasicEffect effect in mesh.Effects)
                {
                    effect.EnableDefaultLighting();
                    effect.World = transforms[mesh.ParentBone.Index] * Matrix.CreateRotationY(modelRotation)
                        * Matrix.CreateTranslation(modelPosition);
                    effect.View = Matrix.CreateLookAt(cameraPosition, Vector3.Zero, Vector3.Up);
                    effect.Projection = Matrix.CreatePerspectiveFieldOfView(MathHelper.ToRadians(45.0f),
                        800/600, 1.0f, 10000.0f);
                }
                // Draw the mesh, using the effects set above.
                mesh.Draw();
            }
        }
    }
}
