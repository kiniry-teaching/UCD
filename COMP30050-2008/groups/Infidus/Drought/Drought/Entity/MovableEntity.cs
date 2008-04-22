using System;
using System.Collections.Generic;
using Microsoft.Xna.Framework;
using Microsoft.Xna.Framework.Graphics;
using Drought.Graphics;
using Drought.World;
using Drought.State;

namespace Drought.Entity
{

    abstract class MovableEntity
    {
        private Vector3 position;

        private Vector3 prevPosition;

        private Vector3 heading;

        private Vector3 normal;

        private Vector3 prevNormal;

        private Matrix orientation;

        private float speed;

        private Path path;

        private Model3D model;

        private LevelInfo levelInfo;
        public LevelInfo LevelInfo { get { return levelInfo; } }
        
        public float radius;

        private bool selected;
        public bool IsSelected { get { return selected; } }
        
        private float selectTime;
        private static readonly float selectTimeStep = 0.025f;

        private LineTool pathTool, ringTool;

        private InfoBox infoBar;

        /** A unique identifier for this entity. */
        public readonly int uniqueID;

        public bool hasMoved;

        private bool prevHasMoved;

        private int health;

        private float water;

        private int maxHealth;

        private float maxWater;

        /* how many updates (if any) this unit is waiting to resolve a collision. */
        private int waiting;

        private Water currWaterPool;

        private float waterSuckAmt;

        private int waterRadius;

        public MovableEntity(GameState gameState, LevelInfo aLevelInfo, Model3D aModel, Path aPath, int uid, float spd, float rad, int maxh, int maxw, float waterSuckAmt, int waterRadius)
        {
            levelInfo = aLevelInfo;
            this.model = aModel;
            path = aPath;
            uniqueID = uid;
            speed = spd;
            radius = rad;
            maxHealth = maxh;
            health = maxh;
            maxWater = maxw;
            water = 0;
            this.waterSuckAmt = waterSuckAmt;
            this.waterRadius = waterRadius;
            
            position = path.getPosition();
            prevPosition = path.getPosition();
            hasMoved = true;
            waiting = 0;
            heading = new Vector3((float)Math.Cos(uid), (float)Math.Sin(uid), 0);
            normal = levelInfo.getNormal(position.X, position.Y);
            orientation = Matrix.Identity;
            setOrientation();

            selected = false;
            infoBar = new InfoBox(gameState);
            pathTool = new LineTool(gameState.getGraphics());
            ringTool = new LineTool(gameState.getGraphics());
            ringTool.setColor(new Vector3(1.0f, 0.0f, 0.0f));

            rebuildRing();
        }

        private void move()
        {
            if (!path.isFinished() && waiting == 0)
            {
                hasMoved = path.addDistance(speed);
                prevPosition.X = position.X;
                prevPosition.Y = position.Y;
                prevPosition.Z = position.Z;
                position = path.getPosition();
                prevNormal.X = normal.X;
                prevNormal.Y = normal.Y;
                prevNormal.Z = normal.Z;
                normal = levelInfo.getNormal(position.X, position.Y);
                normal.Normalize();

                heading = position - prevPosition;
                heading.Normalize();

                setOrientation();
            }
            if (waiting > 0) waiting--;
        }

        public virtual void update()
        {
            prevHasMoved = hasMoved;
            hasMoved = false;
            if (!isDead())
            {
                move();
                pathTool.setPointsList(path.getRemainingPath());
            }
            if (selected)
            {
                if (hasMoved)
                    rebuildRing();
                selectTime += selectTimeStep;
                if (selectTime > 1) selectTime = 1;
            }
            else
            {
                selectTime -= selectTimeStep;
                if (selectTime < 0) selectTime = 0;
            }


            infoBar.update(position, selectTime, health, maxHealth, (int)water/1000, (int)maxWater/1000);
        }

        public void rebuildRing()
        {
            List<Vector3> pointsList = new List<Vector3>();
            float step = MathHelper.Pi / 16;
            for (float i = 0; i <= 32; i++)
            {
                Vector3 pointy = levelInfo.getPositionAt(position.X + (float)Math.Cos(i * step) * radius, position.Y + (float)Math.Sin(i * step) * radius);
                pointy.Z += 0.25f;
                pointsList.Add(pointy);
            }
            ringTool.setPointsList(pointsList);
        }

        public virtual void render(GraphicsDevice graphics, Camera camera, Sun sun)
        {
            if (!isDead())
                pathTool.render(camera.getViewMatrix(), camera.getProjectionMatrix());

            if (selected)
                ringTool.render(camera.getViewMatrix(), camera.getProjectionMatrix());

            graphics.RenderState.DepthBufferEnable = true;
            graphics.RenderState.AlphaBlendEnable = false;
            graphics.RenderState.AlphaTestEnable = false;

            Matrix[] transforms = new Matrix[model.Model.Bones.Count];
            model.Model.CopyAbsoluteBoneTransformsTo(transforms);

            Matrix worldMatrix = Matrix.CreateScale(model.Scale) * orientation * Matrix.CreateTranslation(position);
            //"sink" the units a bit if they're dead, just to conceptually remove them from play
            if (isDead()) worldMatrix *= Matrix.CreateTranslation(new Vector3(0, 0, -0.5f));

            int i = 0;
            foreach (ModelMesh mesh in model.Model.Meshes)
            {
                foreach (Effect currentEffect in mesh.Effects)
                {
                    currentEffect.CurrentTechnique = model.Effect.Techniques["Textured"];

                    currentEffect.Parameters["xWorldViewProjection"].SetValue(transforms[mesh.ParentBone.Index] * worldMatrix * camera.getViewMatrix() * camera.getProjectionMatrix());
                    currentEffect.Parameters["xWorld"].SetValue(worldMatrix);
                    currentEffect.Parameters["xTexture"].SetValue(model.Textures[i++]);
                    currentEffect.Parameters["xEnableLighting"].SetValue(true);
                    currentEffect.Parameters["xEnableNormals"].SetValue(true);
                    currentEffect.Parameters["xLightPosition"].SetValue(sun.getPosition());
                    currentEffect.Parameters["xLightPower"].SetValue(sun.getPower());
                    currentEffect.Parameters["xGreyScale"].SetValue(isDead());
                }
                mesh.Draw();
            }
        }

        public void renderInfoBox(GraphicsDevice graphics, Camera camera) {
            if (selectTime > 0)
            {
                infoBar.render(graphics, camera.getViewMatrix(), camera.getProjectionMatrix());
            }
        }

        /** Takes "oww" health away from this Entity. */
        public void hurt(int oww)
        {
            health -= oww;

            if (health <= 0) //you died!
            {
                selected = false;
                health = 0;
            }
        }

        /* Tells this unit to wait a certain number of updates before attempting to move again. */
        public void wait(int numUpdates)
        {
            waiting = numUpdates;
            if (waiting < 0) waiting = 0;
        }

        public Vector3 getPosition() { return position; }

        public void setPosition(Vector3 aPosition) { position = aPosition; }

        public Matrix getOrientation() { return orientation; }

        private void setOrientation()
        {
            orientation.Up = normal;
            orientation.Right = Vector3.Cross(orientation.Up, heading);
            orientation.Right = Vector3.Normalize(orientation.Right);
            orientation.Forward = Vector3.Cross(-orientation.Right, orientation.Up);
            orientation.Forward = Vector3.Normalize(orientation.Forward);
        }

        public void setPath(Path aPath) { path = aPath; }

        public Path getPath() { return path; }

        public void setOrientation(Matrix anOrientation) { orientation = anOrientation; }

        public void setSelected(bool aSelected) { selected = aSelected; }

        public bool isDead() { return health <= 0; }

        public void addWater(float amt)
        {
            water += amt;

            if (water > maxWater)
                water = maxWater;
        }

        public void removeAllWater() { water = 0; }

        public bool isFullOfWater() { return water == maxWater; }

        protected void suckTehWaterz()
        {
            checkForWater();
            
            if (currWaterPool != null && !isFullOfWater())
            {
                //some water could be wasted but nobody cares about the environment
                addWater(currWaterPool.removeWater(waterSuckAmt));
            }
        }

        protected void checkForWater()
        {
            if (prevHasMoved && !hasMoved)
            {
                for (int x = -waterRadius; x <= waterRadius; x++)
                    for (int y = -waterRadius; y <= waterRadius; y++)
                    {
                        if (levelInfo.getPoolAt((int)position.X + x, (int)position.Y + y) != null)
                        {
                            currWaterPool = levelInfo.getPoolAt((int)position.X + x, (int)position.Y + y);
                            return;
                        }
                    }

                currWaterPool = null;
            }
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
