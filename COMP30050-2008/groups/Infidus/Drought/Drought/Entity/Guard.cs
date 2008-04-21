using System;
using System.Collections.Generic;
using Microsoft.Xna.Framework;
using Microsoft.Xna.Framework.Graphics;
using Drought.Graphics;
using Drought.State;
using Drought.World;
using Drought.Graphics.Particles;

namespace Drought.Entity
{
    class Guard : MovableEntity
    {
        public static readonly float SPEED = 0.4f;

        public static readonly float RADIUS = 2.0f;

        public static readonly int FULL_HEALTH = 10;

        public static readonly int WATER_CAPACITY = 0;

        public static readonly float ATTACK_RADIUS = 25.0f;

        public static readonly int ATTACK_WAIT_TIME = 320;

        private int timeToWait;
        
        private LineTool attackRadiusTool;

        private MovableEntity attackTarget;
        public MovableEntity AttackTarget
        {
            get { return attackTarget; }
            set { attackTarget = value; }
        }

        private ProjectileManager projectiles;

        public Guard(GameState gameState, LevelInfo levelInfo, ModelLoader modelLoader, Path path, int uid, ProjectileManager proj) :
            base(gameState, levelInfo, modelLoader.getModel3D(modelType.Tank), path, uid, SPEED, RADIUS, FULL_HEALTH, WATER_CAPACITY, 0, 0)
        {
            attackRadiusTool = new LineTool(gameState.getGraphics());
            attackRadiusTool.setColor(Color.Green.ToVector3());
            attackTarget = null;
            projectiles = proj;
        }

        public override void update()
        {
            base.update();

            if (isDead()) return;

            List<Vector3> pointsList = new List<Vector3>();
            float step = MathHelper.Pi / 16;
            for (float i = 0; i <= 32; i++)
            {
                Vector3 pointy = LevelInfo.getPositionAt(getPosition().X + (float)Math.Cos(i * step) * ATTACK_RADIUS, getPosition().Y + (float)Math.Sin(i * step) * ATTACK_RADIUS);
                pointy.Z += 0.25f;
                pointsList.Add(pointy);
            }
            attackRadiusTool.setPointsList(pointsList);
            
            if (timeToWait > 0) timeToWait--;

            if (!hasMoved) //if we stayed still since the last update
            {
                /* attack logic */
                if (timeToWait == 0)
                {
                    //attack!
                    if (attackTarget != null)
                    {
                        projectiles.addProjectile(getPosition(), attackTarget.getPosition());
                        attackTarget.hurt(1);
                        timeToWait = ATTACK_WAIT_TIME;
                        if (attackTarget.isDead()) attackTarget = null;
                    }
                }
            }
            else
            {
                attackTarget = null;
            }
        }

        public override void render(GraphicsDevice graphics, Camera camera, Sun sun)
        {
            base.render(graphics, camera, sun);
            if (IsSelected) attackRadiusTool.render(camera.getViewMatrix(), camera.getProjectionMatrix());
        }

        public bool canSetTarget()
        {
            return timeToWait == 0 && attackTarget == null;
        }
    }
}
