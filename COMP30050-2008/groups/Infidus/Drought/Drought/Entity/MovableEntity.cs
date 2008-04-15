using System;
using System.Collections.Generic;
using System.Text;
using Microsoft.Xna.Framework;
using Microsoft.Xna.Framework.Content;
using Microsoft.Xna.Framework.Graphics;
using Drought.Graphics;
using Drought.World;
using Drought.State;

namespace Drought.Entity
{

    public class MovableEntity
    {
        private Terrain terrain;

        private InfoBox infoBar;

        private Vector3 position;

        private Vector3 prevPosition;

        private Vector3 heading;

        private Vector3 normal;

        private Vector3 prevNormal;

        private Matrix orientation;

        private float velocity;

        private Path path;

        private Model model;

        private Texture2D[] modelTextures;

        private float modelScale;

        private bool selected;

        private LineTool pathTool, ringTool;

        private float radius;

        /** A unique identifier for this entity. */
        public readonly int uniqueID;

        private int health;

        private int water;

        private int maxHealth;

        private int maxWater;



        public MovableEntity(GameState gameState, Model model, Texture2D[] modelTextures, Path path, Terrain terrain, int uid)
        {
            this.terrain = terrain;
            infoBar = new InfoBox(gameState);
            radius = 2.5f;
            modelScale = 0.005f;
            uniqueID = uid;
            this.path = path;
            position = path.getPosition();
            prevPosition = path.getPosition();
            heading = new Vector3((float)Math.Cos(uid), (float)Math.Sin(uid), 0);
            normal = path.getNormal();
            orientation = Matrix.Identity;
            setOrientation();
            velocity = 0.5f;
            this.model = model;
            this.modelTextures = modelTextures;
            selected = false;
            pathTool = new LineTool(gameState.getGraphics());
            ringTool = new LineTool(gameState.getGraphics());
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

        public void setPath(Path path)
        {
            this.path = path;
        }

        public Path getPath()
        {
            return path;
        }

        /*
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
        */

        public void update()
        {
            move();
            pathTool.setPointsList(path.getRemainingPath());
            if (selected) {
                List<Vector3> pointsList = new List<Vector3>();
                float step = MathHelper.Pi/16;
                for (float i = 0; i <= 32; i++) {
                    Vector3 pointy = terrain.getHeightMap().getPositionAt(position.X + (float)Math.Cos(i*step)*radius, position.Y + (float)Math.Sin(i*step)*radius);
                    pointy.Z += 0.25f;
                    pointsList.Add(pointy);
                }
                ringTool.setPointsList(pointsList);
            }
            infoBar.updatePosition(position);
        }

        public void render(GraphicsDevice graphics, SpriteBatch batch, Camera camera, Effect effect, Sun sun)
        {
            pathTool.render(camera.getViewMatrix(), camera.getProjectionMatrix());

            if (selected) {
                ringTool.render(camera.getViewMatrix(), camera.getProjectionMatrix());
                infoBar.render(graphics, camera.getViewMatrix(), camera.getProjectionMatrix());
            }

            graphics.RenderState.DepthBufferEnable = true;
            graphics.RenderState.AlphaBlendEnable = false;
            graphics.RenderState.AlphaTestEnable = false;

            Matrix[] transforms = new Matrix[model.Bones.Count];
            model.CopyAbsoluteBoneTransformsTo(transforms);

            Matrix worldMatrix = Matrix.CreateScale(modelScale) * orientation * Matrix.CreateTranslation(position);

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
                    currentEffect.Parameters["xLightPosition"].SetValue(sun.getPosition());
                    currentEffect.Parameters["xLightPower"].SetValue(sun.getPower());
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

        protected void setVecocity(float vel)
        {
            velocity = vel;
        }

        protected void setRadius(float radius)
        {
            this.radius = radius;
        }

        public float getRadius()
        {
            return radius;
        }

        public void damage(int damage)
        {
            health -= damage;
            
            if (health < 0)
                health = 0;
        }

        public bool isDead()
        {
            return health <= 0;
        }

        public void addWater(int amt)
        {
            water += amt;

            if (water > maxWater)
                water = maxWater;
        }

        public void removeAllWater()
        {
            water = 0;
        }

        public bool isFullOfWater()
        {
            return water == maxWater;
        }

        protected void setMaxHealth(int max)
        {
            maxHealth = max;
        }

        protected void setMaxWater(int max)
        {
            maxWater = max;
        }

        protected void setModelScale(float scale)
        {
            modelScale = scale;
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
