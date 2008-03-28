using System;
using System.Collections.Generic;
using System.Text;
using Microsoft.Xna.Framework;
using Microsoft.Xna.Framework.Content;
using Microsoft.Xna.Framework.Graphics;
using Drought.Graphics;
using Drought.World;

namespace Drought.Entity
{

    public class MovableEntity
    {
        private Vector3 position;

        private Vector3 prevPosition;

        private Vector3 heading;

        private Vector3 destination;

        private Vector3 normal;

        private Vector3 prevNormal;

        private Matrix orientation;

        private float velocity;

        private Path path;

        private Model model;

        private Texture2D[] modelTextures;

        private bool selected;

        private LineTool pathTool, ringTool;

        public readonly float radius;

        /** A unique identifier for this entity. */
        public readonly int uniqueID;

        public MovableEntity(DroughtGame game, Model model, Texture2D[] modelTextures, Path path, int uid)
        {
            radius = 2.5f;
            uniqueID = uid;
            this.path = path;
            position = path.getPosition();
            prevPosition = path.getPosition();
            heading = new Vector3((float)Math.Cos(uid), (float)Math.Sin(uid), 0);
            normal = path.getNormal();
            orientation = Matrix.Identity;
            setOrientation();
            velocity = 0.1f;
            this.model = model;
            this.modelTextures = modelTextures;
            selected = false;
            pathTool = new LineTool(game.GraphicsDevice);
            ringTool = new LineTool(game.GraphicsDevice);
            ringTool.setColor(new Vector3(1.0f, 0.0f, 0.0f));
        }

        private void move()
        {
            if (!path.isFinished()) {
                path.addDistance(velocity);
                prevPosition.X = position.X;
                prevPosition.Y = position.Y;
                prevPosition.Z = position.Z;
                position = path.getPosition();
                prevNormal.X = normal.X;
                prevNormal.Y = normal.Y;
                prevNormal.Z = normal.Z;
                normal = path.getNormal();
                normal.Normalize();

                heading = position - prevPosition;
                heading.Normalize();

                setOrientation();
            }
        }

        private void setOrientation()
        {
            orientation.Up = normal;
            orientation.Right = Vector3.Cross(orientation.Up, heading);
            orientation.Right = Vector3.Normalize(orientation.Right);
            orientation.Forward = Vector3.Cross(-orientation.Right, orientation.Up);
            orientation.Forward = Vector3.Normalize(orientation.Forward);
        }

        public void setDestination(Vector3 newDestination)
        {
            destination = newDestination;
        }

        public void setPath(Path path)
        {
            this.path = path;
        }

        public Path getPath()
        {
            return path;
        }

        public void computeNewPath(HeightMap heightMap, NormalMap normalMap)
        {
            List<Vector3> newPathList = new List<Vector3>();
            newPathList.Add(position);
            Vector3 startPos = position;
            Vector3 endPos = destination;
            Vector3 distLeft = endPos - startPos;
            Vector3 currPos = startPos;
            int steps = 0;
            while (distLeft.Length() > 1 && steps < 1000) {
                Vector3 distCopy = new Vector3(distLeft.X, distLeft.Y, distLeft.Z);
                currPos = currPos + Vector3.Normalize(distCopy);
                currPos.Z = heightMap.getHeight(currPos.X, currPos.Y);
                newPathList.Add(currPos);
                distLeft = endPos - currPos;
                steps++;
            }
            newPathList.Add(endPos);

            Path newPath = new Path(newPathList, normalMap);
            setPath(newPath);
        }

        public void update()
        {
            move();
            pathTool.setPointsList(path.getRemainingPath());
            if (selected) {
                List<Vector3> pointsList = new List<Vector3>();
                float step = MathHelper.Pi/16;
                for (float i = 0; i <= 32; i++) {
                    Vector3 pointy = new Vector3(position.X + (float)Math.Cos(i*step) * radius, position.Y + (float)Math.Sin(i*step) * radius, position.Z);
                    pointsList.Add(pointy);
                }
                ringTool.setPointsList(pointsList);
            }
        }

        public void render(GraphicsDevice graphics, SpriteBatch batch, Camera camera, Effect effect)
        {
            pathTool.render(camera.getViewMatrix(), camera.getProjectionMatrix());

            
            if (selected) {
                graphics.RenderState.DepthBufferEnable = false;
                ringTool.render(camera.getViewMatrix(), camera.getProjectionMatrix());
                graphics.RenderState.DepthBufferEnable = true;
            }

            graphics.RenderState.DepthBufferEnable = true;
            graphics.RenderState.AlphaBlendEnable = false;
            graphics.RenderState.AlphaTestEnable = false;

            Matrix[] transforms = new Matrix[model.Bones.Count];
            model.CopyAbsoluteBoneTransformsTo(transforms);

            Matrix worldMatrix = orientation * Matrix.CreateTranslation(position);

            int i = 0;
            foreach (ModelMesh mesh in model.Meshes) {
                foreach (Effect currentEffect in mesh.Effects) {
                    currentEffect.CurrentTechnique = effect.Techniques["Textured"];

                    currentEffect.Parameters["xWorldViewProjection"].SetValue(transforms[mesh.ParentBone.Index] * worldMatrix * camera.getViewMatrix() * camera.getProjectionMatrix());
                    currentEffect.Parameters["xWorld"].SetValue(worldMatrix);
                    currentEffect.Parameters["xTexture"].SetValue(modelTextures[i++]);

                    //HLSL testing
                    //HardCoded Light params need to be replaced with the values from the Sun.
                    currentEffect.Parameters["xEnableLighting"].SetValue(true);
                    currentEffect.Parameters["xLightPosition"].SetValue(new Vector3(0, 0, 200));
                    currentEffect.Parameters["xLightPower"].SetValue(1);
                }
                mesh.Draw();
            }
        }

        public Vector3 getPosition()
        {
            return position;
        }

        public void setPosition(Vector3 aPosition)
        {
            position = aPosition;
        }

        public Matrix getOrientation()
        {
            return orientation;
        }

        public void setOrientation(Matrix anOrientation)
        {
            orientation = anOrientation;
        }

        public void setSelected(bool selected)
        {
            this.selected = selected;
        }

        public bool isSelected()
        {
            return selected;
        }

        /* Given 2 MovableEntities, check whether they overlap. */
        public static bool checkStaticCollision(MovableEntity a, MovableEntity b)
        {
            float xDiff = a.position.X - b.position.X;
            float yDiff = a.position.Y - b.position.Y;
            double dist = Math.Sqrt(xDiff * xDiff + yDiff * yDiff);
            return (dist < a.radius + b.radius);
        }
    }
}
