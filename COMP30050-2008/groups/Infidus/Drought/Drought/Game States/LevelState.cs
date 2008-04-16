using System;
using System.Collections.Generic;
using Microsoft.Xna.Framework;
using Microsoft.Xna.Framework.Graphics;
using Drought.State;
using Drought.Graphics;
using Drought.World;
using Drought.Entity;
using Drought.Input;
using Drought.Sound;

namespace Drought.GameStates
{

    class LevelState : GameState
    {
        private DeviceInput input;

        private Camera camera;

        private Skybox skybox;

        private Terrain terrain; 
        
        private Sun sun;
        private bool sunpause;

        private PlaneParticleEmitter rain;

        private HeightMap heightMap;

        private TextureMap textureMap;

        private NormalMap normalMap;

        private LevelInfo levelInfo;

        private AStar aStar;

        private List<MovableEntity> entities;

        private bool selectCurrent;
        private bool commandCurrent;
        private bool spawnCurrent;
        private bool deleteCurrent;

        private int startClickX, startClickY;
        private int currClickX, currClickY;
        private int selectTimer;

        private LineTool lineTool;

        private ModelLoader modelLoader;

        private SoundManager soundManager;

        public LevelState(IStateManager manager, DroughtGame game, Level aLevel)
            : base(manager, game)
        {
            soundManager = game.getSoundManager();

            input = DeviceInput.getInput();
            heightMap = new HeightMap(aLevel);
            textureMap = new TextureMap(aLevel);
            normalMap = new NormalMap(heightMap);

            levelInfo = new LevelInfo();
            levelInfo.initialise(aLevel);

            aStar = new AStar(levelInfo);

            rain = new PlaneParticleEmitter(512, 256, new Vector3(256, 128, 200), new Vector3(0, 0, 0), new Vector3(3f, 0, -19f), Color.LightBlue.ToVector4(), 100000, 9);

            sun = new Sun(new Vector3(0, -200, 200));

            camera = new Camera(this, heightMap);

            terrain = new Terrain(getGraphics(), getContentManager(), heightMap, textureMap, camera);

            soundManager.setListener(camera);

            modelLoader = new ModelLoader(getContentManager(), getGraphics());

            skybox = new Skybox(camera, sun, modelLoader.getModel3D(modelType.Skybox));

            lineTool = new LineTool(getGraphics());

            loadContent();

            initializeEntities();

            foreach (MovableEntity entity in entities)
            {
                soundManager.playSound(SoundHandle.Truck, entity);
            }
        }

        private void initializeEntities()
        {
            entities = new List<MovableEntity>();
            int uid = 0;
            int hw = heightMap.getMapWidth() / 2;
            int hh = heightMap.getMapHeight() / 2;
            List<Vector3> nodes = new List<Vector3>();
            nodes = new List<Vector3>();
            for (int i = 0; i < 100; i++)
                nodes.Add(heightMap.getPositionAt(hw + i, hh));
            entities.Add(new Tanker(this, modelLoader.getModel3D(modelType.Tank), new Path(nodes, levelInfo), terrain, uid++));
            nodes = new List<Vector3>();
            for (int i = 0; i < 100; i++)
                nodes.Add(heightMap.getPositionAt(hw - i, hh));
            entities.Add(new Tanker(this, modelLoader.getModel3D(modelType.Tank), new Path(nodes, levelInfo), terrain, uid++));
            nodes = new List<Vector3>();
            for (int i = 0; i < 100; i++)
                nodes.Add(heightMap.getPositionAt(hw, hh + i));
            entities.Add(new Tanker(this, modelLoader.getModel3D(modelType.Tank), new Path(nodes, levelInfo), terrain, uid++));
            nodes = new List<Vector3>();
            for (int i = 0; i < 100; i++)
                nodes.Add(heightMap.getPositionAt(hw, hh - i));
            entities.Add(new Tanker(this, modelLoader.getModel3D(modelType.Tank), new Path(nodes, levelInfo), terrain, uid++));
            nodes = new List<Vector3>();
            for (int i = 0; i < 100; i++)
                nodes.Add(heightMap.getPositionAt(hw + i, hh + i));
            entities.Add(new Tanker(this, modelLoader.getModel3D(modelType.Tank), new Path(nodes, levelInfo), terrain, uid++));
            nodes = new List<Vector3>();
            for (int i = 0; i < 100; i++)
                nodes.Add(heightMap.getPositionAt(hw - i, hh - i));
            entities.Add(new Tanker(this, modelLoader.getModel3D(modelType.Tank), new Path(nodes, levelInfo), terrain, uid++));
            nodes = new List<Vector3>();
            for (int i = 0; i < 100; i++)
                nodes.Add(heightMap.getPositionAt(hw + i, hh - i));
            entities.Add(new Tanker(this, modelLoader.getModel3D(modelType.Tank), new Path(nodes, levelInfo), terrain, uid++));
            nodes = new List<Vector3>();
            for (int i = 0; i < 100; i++)
                nodes.Add(heightMap.getPositionAt(hw - i, hh + i));
            entities.Add(new Tanker(this, modelLoader.getModel3D(modelType.Tank), new Path(nodes, levelInfo), terrain, uid++));

            nodes = new List<Vector3>();
            nodes.Add(levelInfo.getPositionAt(1, 1));
            entities.Add(new Tanker(this, modelLoader.getModel3D(modelType.Tank), new Path(nodes, levelInfo), terrain, uid++));
            nodes = new List<Vector3>();
            nodes.Add(levelInfo.getPositionAt(levelInfo.getWidth() - 1, 0));
            entities.Add(new Tanker(this, modelLoader.getModel3D(modelType.Tank), new Path(nodes, levelInfo), terrain, uid++));
            nodes = new List<Vector3>();
            nodes.Add(levelInfo.getPositionAt(0, levelInfo.getHeight() - 1));
            entities.Add(new Tanker(this, modelLoader.getModel3D(modelType.Tank), new Path(nodes, levelInfo), terrain, uid++));
            nodes = new List<Vector3>();
            nodes.Add(levelInfo.getPositionAt(levelInfo.getWidth() - 1, levelInfo.getHeight() - 1));
            entities.Add(new Tanker(this, modelLoader.getModel3D(modelType.Tank), new Path(nodes, levelInfo), terrain, uid++));

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

            sun.update(gameTime);
            camera.update(gameTime);
            terrain.update(gameTime);
            rain.update(gameTime);

            updateUnits();
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

            if (input.isKeyPressed(GameKeys.RESET))
                getStateManager().popState();

            if (input.isKeyPressed(GameKeys.UNIT_SELECT_ALL))
                selectAllUnits();

            if (!sunpause && input.isKeyPressed(GameKeys.PAUSE_SUN))
            {
                sunpause = true;
                sun.isEnabled = !sun.isEnabled;
            }
            else if (sunpause && !input.isKeyPressed(GameKeys.PAUSE_SUN))
            {
                sunpause = false;
            }
        }

        private void updateUnits()
        {
            /* Selecting Units */
            if (!selectCurrent && input.isKeyPressed(GameKeys.UNIT_SELECT))
            {
                selectCurrent = true;
                selectTimer = 0;
                startClickX = input.getMouseX();
                startClickY = input.getMouseY();
                lineTool.setPointsList(new List<Vector3>());
            }
            else if (selectCurrent && !input.isKeyPressed(GameKeys.UNIT_SELECT))
            {
                selectCurrent = false;
                currClickX = input.getMouseX();
                currClickY = input.getMouseY();
                // select a single unit
                if ((startClickX == currClickX && startClickY == currClickY) || selectTimer < 6)
                {
                    //Console.WriteLine("Single Select");
                    Vector3 mousePoint = terrain.projectToTerrain(startClickX, startClickY);
                    if (mousePoint != Terrain.BAD_POSITION)
                    {
                        float minDist = 2.5f;
                        MovableEntity selected = null;
                        foreach (MovableEntity entity in entities)
                        {
                            entity.setSelected(false);
                            Vector3 dist = mousePoint - entity.getPosition();
                            if (dist.Length() < minDist)
                            {
                                minDist = dist.Length();
                                selected = entity;
                            }
                        }
                        if (selected != null) selected.setSelected(true);
                    }
                }
                //select a group of units
                else
                {
                    //Console.WriteLine("Multi Select");
                    int topX = Math.Min(startClickX, currClickX);
                    int topY = Math.Min(startClickY, currClickY);
                    int bottomX = Math.Max(startClickX, currClickX);
                    int bottomY = Math.Max(startClickY, currClickY);
                    Rectangle bounds = new Rectangle(topX, topY, bottomX - topX, bottomY - topY);
                    foreach (MovableEntity entity in entities)
                    {
                        entity.setSelected(false);
                        Vector3 entityPos = terrain.projectToScreen(entity.getPosition());
                        if (entityPos.Z < 1)
                        {
                            if (bounds.Contains(new Point((int)entityPos.X, (int)entityPos.Y)))
                            {
                                entity.setSelected(true);
                            }
                        }
                    }
                }
            }
            if (selectCurrent)
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
            if (!commandCurrent && input.isKeyPressed(GameKeys.UNIT_COMMAND))
            {
                //Console.WriteLine("Commanded Units");
                commandCurrent = true;
                Vector3 mousePoint = terrain.projectToTerrain(input.getMouseX(), input.getMouseY());
                if (mousePoint != Terrain.BAD_POSITION)
                {
                    foreach (MovableEntity entity in entities)
                    {
                        if (entity.isSelected())
                        {
                            bool pathFound;
                            Path p = aStar.computePath(entity.getPosition().X, entity.getPosition().Y, mousePoint.X, mousePoint.Y, out pathFound);
                            if (pathFound)
                                entity.setPath(p);
                        }
                    }
                }
            }
            else if (commandCurrent && !input.isKeyPressed(GameKeys.UNIT_COMMAND))
            {
                commandCurrent = false;
            }

            /* Spawning Units */
            if (!spawnCurrent && input.isKeyPressed(GameKeys.UNIT_SPAWN))
            {
                spawnCurrent = true;
            }
            else if (spawnCurrent && !input.isKeyPressed(GameKeys.UNIT_SPAWN))
            {
                spawnCurrent = false;
                Vector3 mousePoint = terrain.projectToTerrain(input.getMouseX(), input.getMouseY());
                if (mousePoint != Terrain.BAD_POSITION)
                {
                    List<Vector3> dummyPath = new List<Vector3>();
                    dummyPath.Add(mousePoint);
                    MovableEntity newEntity = new Tanker(this, modelLoader.getModel3D(modelType.Tank), new Path(dummyPath, levelInfo), terrain, 0);
                    entities.Add(newEntity);
                    soundManager.playSound(SoundHandle.Truck, newEntity);
                }
            }

            /* Deleting Units */
            if (!deleteCurrent && input.isKeyPressed(GameKeys.UNIT_DELETE))
            {
                deleteCurrent = true;
            }
            else if (deleteCurrent && !input.isKeyPressed(GameKeys.UNIT_DELETE))
            {
                deleteCurrent = false;
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

            for (int i = 0; i < entities.Count; i++)
                entities[i].update();

            for (int i = 0; i < entities.Count; i++)
            {
                MovableEntity a = entities[i];
                for (int j = i + 1; j < entities.Count; j++)
                {
                    MovableEntity b = entities[j];
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
                        aNewPos.Z = heightMap.getHeight(aNewPos.X, aNewPos.Y);
                        a.setPosition(aNewPos);
                        Vector3 bNewPos = b.getPosition() - displacement / 2;
                        bNewPos.Z = heightMap.getHeight(bNewPos.X, bNewPos.Y);
                        b.setPosition(bNewPos);
                        List<Vector3> aPos = new List<Vector3>();
                        aPos.Add(a.getPosition());
                        a.setPath(new Path(aPos, levelInfo));
                        a.hurt(1);
                        List<Vector3> bPos = new List<Vector3>();
                        bPos.Add(b.getPosition());
                        b.setPath(new Path(bPos, levelInfo));
                        b.hurt(1);
                    }
                }
            }
        }

        public void selectAllUnits()
        {
            int topX = 0;
            int topY = 0;
            int bottomX = getGraphics().Viewport.Width;
            int bottomY = getGraphics().Viewport.Height;
            Rectangle bounds = new Rectangle(topX, topY, bottomX - topX, bottomY - topY);
            foreach (MovableEntity entity in entities)
            {
                entity.setSelected(false);
                Vector3 entityPos = terrain.projectToScreen(entity.getPosition());
                if (entityPos.Z < 1)
                {
                    if (bounds.Contains(new Point((int)entityPos.X, (int)entityPos.Y)))
                    {
                        entity.setSelected(true);
                    }
                }
            }
        }

        public override void render(GraphicsDevice graphics, SpriteBatch spriteBatch)
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

            if (selectCurrent)
            {
                lineTool.render();
            }
        }
    }
}
