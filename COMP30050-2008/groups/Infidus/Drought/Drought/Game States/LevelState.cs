using System;
using System.Collections.Generic;
using Microsoft.Xna.Framework;
using Microsoft.Xna.Framework.Graphics;
using Drought.Entity;
using Drought.Graphics;
using Drought.Input;
using Drought.Sound;
using Drought.State;
using Drought.World;
using Drought.Graphics.Particles;

namespace Drought.GameStates
{

    class LevelState : GameState
    {
        /* Temp */
        ExplosionParticleSystem explosionParticles;
        ExplosionSmokeParticleSystem explosionSmokeParticles;
        ProjectileTrailParticleSystem projectileTrailParticles;
        SmokePlumeParticleSystem smokePlumeParticles;
        FireParticleSystem fireParticles;
        ProjectileManager projectileManager;

        private DeviceInput input;

        private int startClickX, startClickY;
        private int currClickX, currClickY;
        private int selectTimer;

        private LevelInfo levelInfo; 
        
        public Camera camera;

        private Terrain terrain;

        private Water[] waters;

        protected Sun sun;

        protected PlaneParticleEmitter rain;

        private Skybox skybox;

        private List<MovableEntity> entities;

        private ModelLoader modelLoader;

        private LineTool lineTool;

        private AStar aStar;

        private SoundManager soundManager;

        public LevelState(IStateManager manager, DroughtGame game, Level aLevel)
            : base(manager, game)
        {
            /* TEMP */
            explosionParticles = new ExplosionParticleSystem(getContentManager(), getGraphics());
            explosionSmokeParticles = new ExplosionSmokeParticleSystem(getContentManager(), getGraphics());
            projectileTrailParticles = new ProjectileTrailParticleSystem(getContentManager(), getGraphics());
            smokePlumeParticles = new SmokePlumeParticleSystem(getContentManager(), getGraphics());
            fireParticles = new FireParticleSystem(getContentManager(), getGraphics());
            projectileManager = new ProjectileManager(explosionParticles, explosionSmokeParticles, projectileTrailParticles);

            soundManager = game.getSoundManager();

            input = DeviceInput.getInput();

            sun = new Sun(new Vector3(0, -200, 200)); 

            levelInfo = new LevelInfo();
            levelInfo.initialise(aLevel);

            TextureMap textureMap = new TextureMap(aLevel);
            //List<List<Vector3>> waterList = Water.findWater(levelInfo);
            List<List<Vector3>> waterListPleh = textureMap.findWater();
            //waters = new Water[waterList.Count];
            waters = new Water[waterListPleh.Count];

            Water[,] waterLocationTable = new Water[levelInfo.getWidth(), levelInfo.getHeight()];
            for (int i = 0; i < waters.Length; i++)
            {
                //waters[i] = new Water(waterList[i], levelInfo, getGraphics());
                waters[i] = new Water(waterListPleh[i], levelInfo, sun, getGraphics());

                for (int j = 0; j < waterListPleh[i].Count; j++)
                {
                    Vector3 p = waterListPleh[i][j];
                    waterLocationTable[(int)p.X, (int)p.Y] = waters[i];
                }
            }
            levelInfo.setWaterPools(waterLocationTable);

            camera = new Camera(this, levelInfo, false);

            rain = new PlaneParticleEmitter(512, 256, new Vector3(256, 128, 200), new Vector3(0, 0, 0), new Vector3(3f, 0, -19f), Color.LightBlue.ToVector4(), 10000, 9);

            terrain = new Terrain(getGraphics(), getContentManager(), levelInfo, camera);

            modelLoader = new ModelLoader(getContentManager(), getGraphics());

            skybox = new Skybox(camera, sun, modelLoader.getModel3D(modelType.Skybox));

            lineTool = new LineTool(getGraphics());

            aStar = new AStar(levelInfo);

            soundManager.setListener(camera);

            loadContent();

            initializeEntities();

            foreach (MovableEntity entity in entities)
                soundManager.playSound(SoundHandle.Truck, entity);
        }

        private void initializeEntities()
        {
            entities = new List<MovableEntity>();
            /*
            int uid = 0;
            int hw = levelInfo.getWidth() / 2;
            int hh = levelInfo.getHeight() / 2;
            List<Vector3> nodes = new List<Vector3>();
            nodes = new List<Vector3>();
            for (int i = 0; i < 100; i++)
                nodes.Add(levelInfo.getPositionAt(hw + i, hh));
            nodes.Reverse();
            entities.Add(new Scout(this, levelInfo, modelLoader, new Path(nodes), uid++));
            nodes = new List<Vector3>();
            for (int i = 0; i < 100; i++)
                nodes.Add(levelInfo.getPositionAt(hw - i, hh));
            nodes.Reverse();
            entities.Add(new Tanker(this, levelInfo, modelLoader, new Path(nodes), uid++));
            nodes = new List<Vector3>();
            for (int i = 0; i < 100; i++)
                nodes.Add(levelInfo.getPositionAt(hw, hh + i));
            nodes.Reverse();
            entities.Add(new Scout(this, levelInfo, modelLoader, new Path(nodes), uid++));
            nodes = new List<Vector3>();
            for (int i = 0; i < 100; i++)
                nodes.Add(levelInfo.getPositionAt(hw, hh - i));
            nodes.Reverse();
            entities.Add(new Scout(this, levelInfo, modelLoader, new Path(nodes), uid++));
            nodes = new List<Vector3>();
            for (int i = 0; i < 100; i++)
                nodes.Add(levelInfo.getPositionAt(hw + i, hh + i));
            nodes.Reverse();
            entities.Add(new Scout(this, levelInfo, modelLoader, new Path(nodes), uid++));
            nodes = new List<Vector3>();
            for (int i = 0; i < 100; i++)
                nodes.Add(levelInfo.getPositionAt(hw - i, hh - i));
            nodes.Reverse();
            entities.Add(new Guard(this, levelInfo, modelLoader, new Path(nodes), uid++, projectileManager));
            nodes = new List<Vector3>();
            for (int i = 0; i < 100; i++)
                nodes.Add(levelInfo.getPositionAt(hw + i, hh - i));
            nodes.Reverse();
            entities.Add(new Guard(this, levelInfo, modelLoader, new Path(nodes), uid++, projectileManager));
            nodes = new List<Vector3>();
            for (int i = 0; i < 100; i++)
                nodes.Add(levelInfo.getPositionAt(hw - i, hh + i));
            nodes.Reverse();
            entities.Add(new Guard(this, levelInfo, modelLoader, new Path(nodes), uid++, projectileManager));

            nodes = new List<Vector3>();
            nodes.Add(levelInfo.getPositionAt(1, 1));
            entities.Add(new Guard(this, levelInfo, modelLoader, new Path(nodes), uid++, projectileManager));
            nodes = new List<Vector3>();
            nodes.Add(levelInfo.getPositionAt(levelInfo.getWidth() - 1, 1));
            entities.Add(new Guard(this, levelInfo, modelLoader, new Path(nodes), uid++, projectileManager));
            nodes = new List<Vector3>();
            nodes.Add(levelInfo.getPositionAt(1, levelInfo.getHeight() - 1));
            entities.Add(new Guard(this, levelInfo, modelLoader, new Path(nodes), uid++, projectileManager));
            nodes = new List<Vector3>();
            nodes.Add(levelInfo.getPositionAt(levelInfo.getWidth() - 1, levelInfo.getHeight() - 1));
            entities.Add(new Guard(this, levelInfo, modelLoader, new Path(nodes), uid++, projectileManager));
            */

        }

        public override void loadContent()
        {
            terrain.loadContent();

            rain.loadContent(getContentManager());
        }

        public override void background()
        {
            //Console.WriteLine("LevelState in background");
        }

        public override void foreground()
        {
            //Console.WriteLine("LevelState in foreground");
        }

        public override void update(GameTime gameTime)
        {
            updateInput();
            updateUnitInput();
            
            sun.update(gameTime);
            camera.update();
            rain.update();

            for (int i = 0; i < waters.Length; i++) 
                waters[i].update(gameTime);

            updateUnits();
            updateParticles(gameTime);
        }

        private void updateInput()
        {
            if (input.isKeyPressed(GameKeys.CAM_FORWARD))
                camera.forward();
            else if (input.isKeyPressed(GameKeys.CAM_BACK))
                camera.back();

            if (input.isKeyPressed(GameKeys.CAM_LEFT))
                camera.left();
            else if (input.isKeyPressed(GameKeys.CAM_RIGHT))
                camera.right();

            if (input.isKeyPressed(GameKeys.CAM_ASCEND))
                camera.ascend();
            else if (input.isKeyPressed(GameKeys.CAM_DESCEND))
                camera.descend();

            if (input.isKeyPressed(GameKeys.CAM_ZOOM_IN))
                camera.zoomIn();
            else if (input.isKeyPressed(GameKeys.CAM_ZOOM_OUT))
                camera.zoomOut();

            if (input.isKeyPressed(GameKeys.CAM_ROTATE_UP))
                camera.rotateUp();
            else if (input.isKeyPressed(GameKeys.CAM_ROTATE_DOWN))
                camera.rotateDown();

            if (input.isKeyPressed(GameKeys.CAM_ROTATE_LEFT))
                camera.rotateLeft();
            else if (input.isKeyPressed(GameKeys.CAM_ROTATE_RIGHT))
                camera.rotateRight();

            if (input.wasKeyJustPressed(GameKeys.RESET))
                getStateManager().popState();

            if (input.wasKeyJustPressed(GameKeys.UNIT_SELECT_ALL))
                selectAllUnits();

            if (input.wasKeyJustPressed(GameKeys.PAUSE_SUN))
                sun.isEnabled = !sun.isEnabled;

            if (input.isKeyPressed(GameKeys.BURN_BABY_BURN))
            {
                const int fireParticlesPerFrame = 20;
                for (int i = 0; i < fireParticlesPerFrame; i++)
                {
                    fireParticles.AddParticle(randomFirePosition(), Vector3.Zero);
                }
                smokePlumeParticles.AddParticle(randomFirePosition(), Vector3.Zero);
            }
        }

        private Vector3 randomFirePosition()
        {
            Random random = new Random();
            Vector3 terrainSurface = terrain.projectToTerrain(input.getMouseX(), input.getMouseY());
            
            terrainSurface.X += (float) Math.Sqrt((random.NextDouble() * 10) - 5);
            terrainSurface.Y += (float)Math.Sqrt((random.NextDouble() * 10) - 5);
            terrainSurface.Z += (float)Math.Abs(Math.Sqrt((random.NextDouble() * 10) - 5));

            //const float radius = 30;
            //const float height = 40;
            //double angle = random.NextDouble() * Math.PI * 2;
            //float x = (float)Math.Cos(angle);
            //float y = (float)Math.Sin(angle);
            //terrainSurface += new Vector3(x * radius, y * radius + height, 10);

            return terrainSurface;
        }

        private void updateUnitInput()
        {
            /* Selecting Units */
            if (input.wasKeyJustPressed(GameKeys.UNIT_SELECT))
            {
                selectTimer = 0;
                startClickX = input.getMouseX();
                startClickY = input.getMouseY();
                lineTool.setPointsList(new List<Vector3>());
            }
            else if (input.wasKeyJustReleased(GameKeys.UNIT_SELECT))
            {
                currClickX = input.getMouseX();
                currClickY = input.getMouseY();
                // select a single unit
                if ((startClickX == currClickX && startClickY == currClickY) || selectTimer < 6)
                {
                    Vector3 mousePoint = terrain.projectToTerrain(startClickX, startClickY);
                    if (mousePoint != Terrain.BAD_POSITION)
                    {
                        float minDist = 2.5f;
                        MovableEntity selected = null;
                        foreach (MovableEntity entity in entities)
                        {
                            entity.setSelected(false);
                            if (!entity.isDead())
                            {
                                Vector3 dist = mousePoint - entity.getPosition();
                                if (dist.Length() < minDist)
                                {
                                    minDist = dist.Length();
                                    selected = entity;
                                }
                            }
                        }
                        if (selected != null) selected.setSelected(true);
                    }
                }
                //select a group of units
                else
                {
                    int topX = Math.Min(startClickX, currClickX);
                    int topY = Math.Min(startClickY, currClickY);
                    int bottomX = Math.Max(startClickX, currClickX);
                    int bottomY = Math.Max(startClickY, currClickY);
                    Rectangle bounds = new Rectangle(topX, topY, bottomX - topX, bottomY - topY);
                    foreach (MovableEntity entity in entities)
                    {
                        entity.setSelected(false);
                        if (!entity.isDead())
                        {
                            Vector3 entityPos = terrain.projectToScreen(entity.getPosition());
                            if (entityPos.Z < 1 && bounds.Contains(new Point((int)entityPos.X, (int)entityPos.Y)))
                                entity.setSelected(true);
                        }
                    }
                }
            }
            if (input.isKeyPressed(GameKeys.UNIT_SELECT))
            {
                selectTimer++;
                currClickX = input.getMouseX();
                currClickY = input.getMouseY();
                if (selectTimer >= 6)
                {
                    int screenX = getGraphics().Viewport.Width / 2;
                    int screenY = getGraphics().Viewport.Height / 2;
                    List<Vector3> boundingBox = new List<Vector3>();
                    boundingBox.Add(new Vector3((startClickX - screenX) / (float)screenX, -(startClickY - screenY) / (float)screenY, 0));
                    boundingBox.Add(new Vector3((currClickX - screenX) / (float)screenX, -(startClickY - screenY) / (float)screenY, 0));
                    boundingBox.Add(new Vector3((currClickX - screenX) / (float)screenX, -(currClickY - screenY) / (float)screenY, 0));
                    boundingBox.Add(new Vector3((startClickX - screenX) / (float)screenX, -(currClickY - screenY) / (float)screenY, 0));
                    boundingBox.Add(new Vector3((startClickX - screenX) / (float)screenX, -(startClickY - screenY) / (float)screenY, 0));
                    lineTool.setPointsList(boundingBox);
                }
            }

            /* Commanding Units */
            if (input.wasKeyJustPressed(GameKeys.UNIT_COMMAND))
            {
                Vector3 mousePoint = terrain.projectToTerrain(input.getMouseX(), input.getMouseY());
                if (mousePoint != Terrain.BAD_POSITION)
                {
                    foreach (MovableEntity entity in entities)
                    {
                        if (entity.IsSelected)
                        {
                            bool pathFound;
                            Path p = aStar.computePath(entity.getPosition().X, entity.getPosition().Y, mousePoint.X, mousePoint.Y, out pathFound);
                            if (pathFound)
                                entity.setPath(p);
                        }
                    }
                }
            }

            /* Spawning Units */
            if (input.wasKeyJustReleased(GameKeys.UNIT_SPAWN_GUARD))
            {
                Vector3 mousePoint = terrain.projectToTerrain(input.getMouseX(), input.getMouseY());
                if (mousePoint != Terrain.BAD_POSITION)
                {
                    List<Vector3> dummyPath = new List<Vector3>();
                    dummyPath.Add(mousePoint);
                    MovableEntity newEntity = new Guard(this, levelInfo, modelLoader, new Path(dummyPath), 0, projectileManager);
                    entities.Add(newEntity);
                    soundManager.playSound(SoundHandle.Truck, newEntity);
                }
            }
            else if (input.wasKeyJustReleased(GameKeys.UNIT_SPAWN_SCOUT))
            {
                Vector3 mousePoint = terrain.projectToTerrain(input.getMouseX(), input.getMouseY());
                if (mousePoint != Terrain.BAD_POSITION)
                {
                    List<Vector3> dummyPath = new List<Vector3>();
                    dummyPath.Add(mousePoint);
                    MovableEntity newEntity = new Scout(this, levelInfo, modelLoader, new Path(dummyPath), 0);
                    entities.Add(newEntity);
                    soundManager.playSound(SoundHandle.Truck, newEntity);
                }
            }
            else if (input.wasKeyJustReleased(GameKeys.UNIT_SPAWN_TANKER))
            {
                Vector3 mousePoint = terrain.projectToTerrain(input.getMouseX(), input.getMouseY());
                if (mousePoint != Terrain.BAD_POSITION)
                {
                    List<Vector3> dummyPath = new List<Vector3>();
                    dummyPath.Add(mousePoint);
                    MovableEntity newEntity = new Tanker(this, levelInfo, modelLoader, new Path(dummyPath), 0);
                    entities.Add(newEntity);
                    soundManager.playSound(SoundHandle.Truck, newEntity);
                }
            }

            /* Deleting Units */
            if (input.wasKeyJustReleased(GameKeys.UNIT_DELETE))
            {
                Vector3 mousePoint = terrain.projectToTerrain(input.getMouseX(), input.getMouseY());
                if (mousePoint != Terrain.BAD_POSITION)
                {
                    float minDist = 5.0f;
                    MovableEntity deleted = null;
                    foreach (MovableEntity entity in entities)
                    {
                        Vector3 dist = mousePoint - entity.getPosition();
                        if (dist.Length() < minDist)
                        {
                            minDist = dist.Length();
                            deleted = entity;
                        }
                    }
                    if (deleted != null) entities.Remove(deleted);
                }
            }
        }

        private void updateUnits()
        {
            for (int i = 0; i < entities.Count; i++)
                entities[i].update();

            for (int i = 0; i < entities.Count; i++)
            {
                MovableEntity a = entities[i];
                for (int j = i + 1; j < entities.Count; j++)
                {
                    MovableEntity b = entities[j];
                    //if (a.wasUpdated || b.wasUpdated)
                    if (MovableEntity.checkStaticCollision(a, b))
                    {
                        float xDiff = a.getPosition().X - b.getPosition().X;
                        float yDiff = a.getPosition().Y - b.getPosition().Y;
                        Vector3 diff = new Vector3(xDiff, yDiff, 0);
                        Vector3 dist = diff;

                        if (diff.Length() != 0)
                            diff.Normalize();

                        diff *= a.radius + b.radius;
                        Vector3 displacement = diff - dist;
                        Vector3 aNewPos = a.getPosition() + displacement / 2;
                        aNewPos.Z = levelInfo.getHeight(aNewPos.X, aNewPos.Y);
                        a.setPosition(aNewPos);
                        a.rebuildRing();
                        Vector3 bNewPos = b.getPosition() - displacement / 2;
                        bNewPos.Z = levelInfo.getHeight(bNewPos.X, bNewPos.Y);
                        b.setPosition(bNewPos);
                        b.rebuildRing();
                    }
                }
                if (a is Guard && ((Guard)a).canSetTarget())
                {
                    float minDist = float.MaxValue;
                    MovableEntity newTarget = null;
                    for (int j = 0; j < entities.Count; j++)
                    {
                        if (j == i) continue; //don't target yourself!
                        MovableEntity b = entities[j];
                        if (b.isDead()) continue; //don't target dead units
                        float diff = Vector3.DistanceSquared(a.getPosition(), b.getPosition());
                        if (diff < minDist)
                        {
                            minDist = diff;
                            newTarget = b;
                        }
                    }
                    if (newTarget != null && minDist <= Guard.ATTACK_RADIUS * Guard.ATTACK_RADIUS)
                        ((Guard)a).AttackTarget = newTarget;
                }
            }
        }

        public void selectAllUnits()
        {
            Rectangle bounds = new Rectangle(0, 0, getGraphics().Viewport.Width, getGraphics().Viewport.Height);
            foreach (MovableEntity entity in entities)
                if (!entity.isDead())
                {
                    entity.setSelected(false);
                    Vector3 entityPos = terrain.projectToScreen(entity.getPosition());
                        if (entityPos.Z < 1 && bounds.Contains(new Point((int)entityPos.X, (int)entityPos.Y)))
                            entity.setSelected(true);
                }
        }

        private void updateParticles(GameTime gameTime)
        {
            Matrix view = camera.getViewMatrix();
            Matrix projection = camera.getProjectionMatrix();

            explosionParticles.SetCamera(view, projection);
            explosionSmokeParticles.SetCamera(view, projection);
            projectileTrailParticles.SetCamera(view, projection);
            smokePlumeParticles.SetCamera(view, projection);
            fireParticles.SetCamera(view, projection);

            explosionParticles.update(gameTime);
            explosionSmokeParticles.update(gameTime);
            projectileTrailParticles.update(gameTime);
            smokePlumeParticles.update(gameTime);
            fireParticles.update(gameTime);

            projectileManager.update(gameTime);
        }

        public override void render(GameTime gameTime, GraphicsDevice graphics, SpriteBatch spriteBatch)
        {
            graphics.RenderState.FillMode = FillMode.Solid;
            graphics.RenderState.CullMode = CullMode.None;

            graphics.SamplerStates[0].AddressU = TextureAddressMode.Wrap;
            graphics.SamplerStates[0].AddressV = TextureAddressMode.Wrap;

            graphics.RenderState.DepthBufferEnable = true;
            graphics.RenderState.AlphaBlendEnable = false;
            graphics.RenderState.AlphaTestEnable = false;

            graphics.Clear(ClearOptions.DepthBuffer, Color.Black, 1.0f, 0);

            terrain.render(sun);
            skybox.render();
            rain.render(graphics, camera.getViewMatrix(), camera.getProjectionMatrix());

            for (int i = 0; i < entities.Count; i++)
                entities[i].render(graphics, camera, sun);
            for (int i = 0; i < entities.Count; i++)
                entities[i].renderInfoBox(graphics, camera);
            
            foreach (Water w in waters)
                w.render(graphics, camera.getViewMatrix(), camera.getProjectionMatrix());

            if (input.isKeyPressed(GameKeys.UNIT_SELECT))
                lineTool.render();

            explosionParticles.render(gameTime, graphics);
            explosionSmokeParticles.render(gameTime, graphics);
            projectileTrailParticles.render(gameTime, graphics);
            smokePlumeParticles.render(gameTime, graphics);
            fireParticles.render(gameTime, graphics);
        }
    }
}
