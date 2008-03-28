using System;
using System.Collections.Generic;
using Microsoft.Xna.Framework;
using Microsoft.Xna.Framework.Graphics;
using Drought.State;
using Drought.Graphics;
using Drought.World;
using Drought.Entity;
using Drought.Input;
using Drought.Network;
using Drought.Sound;

namespace Drought.GameStates
{
    /** 
     * Branch of LevelState; a testbed for early networking functions,
     * so any broken functionality won't impede others' efforts.
     */
    class NetLevelState : GameState 
    {
        private Terrain terrain;

        private Skybox skybox;

        private Sun sun;

        private Camera camera;

        private HeightMap heightMap;

        private TextureMap textureMap;

        private WaterMap waterMap;

        private NormalMap normalMap;

        private DeviceInput input;

        private Effect modelEffect;

        private List<MovableEntity> localEntities;

        private List<MovableEntity> remoteEntities;

        private bool selectCurrent;
        private bool commandCurrent;
        private bool spawnCurrent;
        private bool deleteCurrent;

        private int startClickX, startClickY;
        private int currClickX, currClickY;
        private int selectTimer;

        private LineTool lineTool;

        private ModelLoader modelLoader;

        private NetworkManager networkManager;
        private bool hosting;

        public NetLevelState(IStateManager manager, DroughtGame game, Level aLevel, bool isHost) :
            base(manager, game)
        {
            networkManager = game.getNetworkManager();
            hosting = isHost;

            input = DeviceInput.getInput();
            heightMap = new HeightMap(aLevel);
            textureMap = new TextureMap(aLevel);
            normalMap = new NormalMap(heightMap);
            waterMap = new WaterMap(heightMap, textureMap);

            camera = new Camera(game, heightMap);
            
            terrain = new Terrain(getGraphics(), getContentManager(), heightMap, textureMap, camera);

            sun = new Sun(new Vector3(0, -200, 0));

            game.getSoundManager().setListener(camera);

            skybox = new Skybox(camera);

            modelLoader = new ModelLoader(getContentManager(), game.getGraphics());

            lineTool = new LineTool(getGraphics());

            loadContent();

            initializeEntities();

            foreach (MovableEntity entity in localEntities) {
                game.getSoundManager().playSound(SoundHandle.Truck, entity);
            }
        }

        private void initializeEntities()
        {
            localEntities = new List<MovableEntity>();
            int uid = 0;
            if (!hosting) uid = 3;
            List<Vector3> nodes = new List<Vector3>();
            for (int i = 100; i < 200; i++)
                nodes.Add(heightMap.getPositionAt(i, i));
            localEntities.Add(new MovableEntity(getGame(), modelLoader.getModel(modelType.Car), modelLoader.getModelTextures(modelType.Car), new Path(nodes, normalMap), uid++));

            nodes = new List<Vector3>();
            for (int i = 100; i < 200; i++)
                nodes.Add(heightMap.getPositionAt(i, 200));
            localEntities.Add(new MovableEntity(getGame(), modelLoader.getModel(modelType.Car), modelLoader.getModelTextures(modelType.Car), new Path(nodes, normalMap), uid++));

            nodes = new List<Vector3>();
            for (int i = 100; i < 200; i++)
                nodes.Add(heightMap.getPositionAt(200, i));
            localEntities.Add(new MovableEntity(getGame(), modelLoader.getModel(modelType.Car), modelLoader.getModelTextures(modelType.Car), new Path(nodes, normalMap), uid++));

            if (!hosting) uid = 0;
            remoteEntities = new List<MovableEntity>();
            nodes = new List<Vector3>();
            for (int i = 100; i > 0; i--)
                nodes.Add(heightMap.getPositionAt(i, i));
            remoteEntities.Add(new MovableEntity(getGame(), modelLoader.getModel(modelType.Car), modelLoader.getModelTextures(modelType.Car), new Path(nodes, normalMap), uid++));

            nodes = new List<Vector3>();
            for (int i = 100; i > 0; i--)
                nodes.Add(heightMap.getPositionAt(i, 200));
            remoteEntities.Add(new MovableEntity(getGame(), modelLoader.getModel(modelType.Car), modelLoader.getModelTextures(modelType.Car), new Path(nodes, normalMap), uid++));

            nodes = new List<Vector3>();
            for (int i = 100; i > 0; i--)
                nodes.Add(heightMap.getPositionAt(200, i));
            remoteEntities.Add(new MovableEntity(getGame(), modelLoader.getModel(modelType.Car), modelLoader.getModelTextures(modelType.Car), new Path(nodes, normalMap), uid++));
        }

        public override void loadContent()
        {
            modelEffect = getContentManager().Load<Effect>("EffectFiles/model");

            terrain.loadContent();

            skybox.loadContent(getContentManager(), getGraphics());
        }

        public override void background()
        {
            //Console.WriteLine("NetLevelState in background");
            //throw new Exception("The method or operation is not implemented.");
        }

        public override void foreground()
        {
            //Console.WriteLine("NetLevelState in foreground");
            //throw new Exception("The method or operation is not implemented.");
        }

        public override void update(GameTime gameTime)
        {
            updateInput();

            camera.update(gameTime);
            terrain.update(gameTime);

            updateUnits();
            updateNetwork();
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

            if (input.isKeyPressed(GameKeys.ADD_WATER))
                waterMap.addWater(10); 
            
            if (input.isKeyPressed(GameKeys.RESET)) {
                networkManager.disconnect();
                getStateManager().popState();
            }
        }

        private void updateUnits()
        {
            /* Selecting Units */
            if (!selectCurrent && input.isKeyPressed(GameKeys.UNIT_SELECT)) {
                selectCurrent = true;
                selectTimer = 0;
                startClickX = input.getMouseX();
                startClickY = input.getMouseY();
                lineTool.setPointsList(new List<Vector3>());
            }
            else if (selectCurrent && !input.isKeyPressed(GameKeys.UNIT_SELECT)) {
                selectCurrent = false;
                currClickX = input.getMouseX();
                currClickY = input.getMouseY();
                // select a single unit
                if ((startClickX == currClickX && startClickY == currClickY) || selectTimer < 6) {
                    //Console.WriteLine("Single Select");
                    Vector3 mousePoint = terrain.projectToTerrain(startClickX, startClickY);
                    float minDist = 2.5f;
                    MovableEntity selected = null;
                    foreach (MovableEntity entity in localEntities) {
                        entity.setSelected(false);
                        Vector3 dist = mousePoint - entity.getPosition();
                        if (dist.Length() < minDist) {
                            minDist = dist.Length();
                            selected = entity;
                        }
                    }
                    if (selected != null) selected.setSelected(true);
                }
                //select a group of units
                else {
                    //Console.WriteLine("Multi Select");
                    int topX = Math.Min(startClickX, currClickX);
                    int topY = Math.Min(startClickY, currClickY);
                    int bottomX = Math.Max(startClickX, currClickX);
                    int bottomY = Math.Max(startClickY, currClickY);
                    Rectangle bounds = new Rectangle(topX, topY, bottomX - topX, bottomY - topY);
                    foreach (MovableEntity entity in localEntities) {
                        entity.setSelected(false);
                        Vector3 entityPos = terrain.projectToScreen(entity.getPosition());
                        if (entityPos.Z < 1) {
                            if (bounds.Contains(new Point((int)entityPos.X, (int)entityPos.Y))) {
                                entity.setSelected(true);
                            }
                        }
                    }
                }
            }
            if (selectCurrent) {
                selectTimer++;
                currClickX = input.getMouseX();
                currClickY = input.getMouseY();
                if (selectTimer >= 6) {
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
            if (!commandCurrent && input.isKeyPressed(GameKeys.UNIT_COMMAND)) {
                //Console.WriteLine("Commanded Units");
                commandCurrent = true;
                foreach (MovableEntity entity in localEntities) {
                    if (entity.isSelected()) {
                        Vector3 clickPoint = terrain.projectToTerrain(input.getMouseX(), input.getMouseY());
                        entity.setDestination(clickPoint);
                        entity.computeNewPath(heightMap, normalMap);
                    }
                }
            }
            else if (commandCurrent && !input.isKeyPressed(GameKeys.UNIT_COMMAND)) {
                commandCurrent = false;
            }

            /* Spawning Units */
            if (!spawnCurrent && input.isKeyPressed(GameKeys.UNIT_SPAWN)) {
                spawnCurrent = true;
            }
            else if (spawnCurrent && !input.isKeyPressed(GameKeys.UNIT_SPAWN)) {
                spawnCurrent = false;
                Vector3 mousePoint = terrain.projectToTerrain(input.getMouseX(), input.getMouseY());
                List<Vector3> dummyPath = new List<Vector3>();
                dummyPath.Add(mousePoint);
                localEntities.Add(new MovableEntity(getGame(), modelLoader.getModel(modelType.Car), modelLoader.getModelTextures(modelType.Car), new Path(dummyPath, normalMap), 0));
            }

            /* Deleting Units */
            if (!deleteCurrent && input.isKeyPressed(GameKeys.UNIT_DELETE)) {
                deleteCurrent = true;
            }
            else if (deleteCurrent && !input.isKeyPressed(GameKeys.UNIT_DELETE)) {
                deleteCurrent = false;
                Vector3 mousePoint = terrain.projectToTerrain(input.getMouseX(), input.getMouseY());
                float minDist = 5.0f;
                MovableEntity deleted = null;
                foreach (MovableEntity entity in localEntities) {
                    Vector3 dist = mousePoint - entity.getPosition();
                    if (dist.Length() < minDist) {
                        minDist = dist.Length();
                        deleted = entity;
                    }
                }
                if (deleted != null) localEntities.Remove(deleted);
            }

            for (int i = 0; i < localEntities.Count; i++)
                localEntities[i].update();

            for (int i = 0; i < localEntities.Count; i++) {
                MovableEntity a = localEntities[i];
                for (int j = i+1; j < localEntities.Count; j++) {
                    MovableEntity b = localEntities[j];
                    if (a == b) Console.WriteLine("fail!");
                    if (a != b && MovableEntity.checkStaticCollision(a, b)) {
                        Vector3 diff = a.getPosition() - b.getPosition();
                        Vector3 diffRad = diff;
                        diffRad.Normalize();
                        diffRad *= a.radius + b.radius;
                        Vector3 displacement = diffRad - diff;
                        a.setPosition(a.getPosition() + displacement/2);
                        b.setPosition(a.getPosition() - displacement/2);
                    }
                }
            }
        }

        public void updateNetwork()
        {
            //TODO: Networking needs some updating, to take into account units being added/deleted

            foreach (MovableEntity entity in localEntities) {
                networkManager.sendPos(entity);
            }

            while (networkManager.hasMoreData()) {
                int uid = networkManager.recieveUID();
                Vector3 pos = networkManager.recievePos();
                Matrix ori = networkManager.recieveOri();
                foreach (MovableEntity entity in remoteEntities)
                    if (entity.uniqueID == uid) {
                        entity.setPosition(pos);
                        entity.setOrientation(ori);
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

            for (int i = 0; i < localEntities.Count; i++)
                localEntities[i].render(graphics, spriteBatch, camera, modelEffect, sun);
            for (int i = 0; i < remoteEntities.Count; i++)
                remoteEntities[i].render(graphics, spriteBatch, camera, modelEffect, sun);

            if (selectCurrent) {
                lineTool.render();
            }
        }
    }
}
