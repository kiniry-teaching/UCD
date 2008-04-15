using System;
using System.Collections.Generic;
using Microsoft.Xna.Framework;
using Microsoft.Xna.Framework.Graphics;
using Drought.Graphics;
using Drought.World;
using Drought.State;

namespace Drought.Entity
{

    class MovableEntity
    {
        private int health, maxHealth;

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

        private Model3D model;

        private bool selected;
        private float selectTime;
        private float selectTimeStep = 0.025f;

        private LineTool pathTool, ringTool;

        public readonly float radius;

        /** A unique identifier for this entity. */
        public readonly int uniqueID;

        public MovableEntity(GameState gameState, Model3D model, Path path, Terrain terrain, int uid)
        {
            health = 5;
            maxHealth = 5;
            this.terrain = terrain;
            infoBar = new InfoBox(gameState);
            radius = 2.5f;
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
                selectTime += selectTimeStep;
                if (selectTime > 1) selectTime = 1;
            }
            else {
                selectTime -= selectTimeStep;
                if (selectTime < 0) selectTime = 0;
            }
            infoBar.update(position, selectTime, health, maxHealth);
        }

        public void render(GraphicsDevice graphics, SpriteBatch batch, Camera camera, Effect effect, Sun sun)
        {
            pathTool.render(camera.getViewMatrix(), camera.getProjectionMatrix());

            if (selected) {
                ringTool.render(camera.getViewMatrix(), camera.getProjectionMatrix());
            }
            if (selectTime > 0) {
                infoBar.render(graphics, camera.getViewMatrix(), camera.getProjectionMatrix());
            }

            graphics.RenderState.DepthBufferEnable = true;
            graphics.RenderState.AlphaBlendEnable = false;
            graphics.RenderState.AlphaTestEnable = false;

            Matrix[] transforms = new Matrix[model.Model.Bones.Count];
            model.Model.CopyAbsoluteBoneTransformsTo(transforms);

            Matrix worldMatrix = Matrix.CreateScale(0.005f) * orientation * Matrix.CreateTranslation(position);

            int i = 0;
            foreach (ModelMesh mesh in model.Model.Meshes) {
                foreach (Effect currentEffect in mesh.Effects) {
                    currentEffect.CurrentTechnique = effect.Techniques["Textured"];

                    currentEffect.Parameters["xWorldViewProjection"].SetValue(transforms[mesh.ParentBone.Index] * worldMatrix * camera.getViewMatrix() * camera.getProjectionMatrix());
                    currentEffect.Parameters["xWorld"].SetValue(worldMatrix);
                    currentEffect.Parameters["xTexture"].SetValue(model.ModelTextures[i++]);
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

        /* Given 2 MovableEntities, check whether they overlap. */
        public static bool checkStaticCollision(MovableEntity a, MovableEntity b)
        {
            float xDiff = a.position.X - b.position.X;
            float yDiff = a.position.Y - b.position.Y;
            double dist = Math.Sqrt(xDiff * xDiff + yDiff * yDiff);
            return (dist < a.radius + b.radius);
        }

        /** Takes "oww" health away from this Entity. */
        public void hurt(int oww)
        {
            health -= oww;
            if (health < 0) health = maxHealth;
        }
    }
}
