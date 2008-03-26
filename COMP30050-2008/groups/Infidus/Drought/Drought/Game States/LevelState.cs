using System;
using System.Collections.Generic;
using Microsoft.Xna.Framework;
using Microsoft.Xna.Framework.Graphics;
using Drought.State;
using Drought.Graphics;
using Drought.World;
using Drought.Entity;
using Drought.Input;

namespace Drought.GameStates
{
    class LevelState : GameState 
    {
        private Terrain terrain;

        private Skybox skybox;

        private Camera camera; 
        
        private HeightMap heightMap;

        private TextureMap textureMap;

        private WaterMap waterMap;

        private NormalMap normalMap;

        private DeviceInput input;

        private Effect modelEffect;

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

        public LevelState(IStateManager manager, DroughtGame game, string fileName) :
            base(manager, game)
        {
            input = DeviceInput.getInput();
            heightMap = new HeightMap(fileName);
            textureMap = new TextureMap(fileName);
            normalMap = new NormalMap(heightMap); 
            waterMap = new WaterMap(heightMap, textureMap);

            camera = new Camera(game, heightMap);

            terrain = new Terrain(getGraphics(), getContentManager(), heightMap, textureMap, camera);

            skybox = new Skybox(camera);

            modelLoader = new ModelLoader(getContentManager(), game.getGraphics());

            lineTool = new LineTool(getGraphics()); 
            
            loadContent();

            initializeEntities();
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
                nodes.Add(new Vector3(hw + i, hh, heightMap.getHeight(hw + i, hh)));
            entities.Add(new MovableEntity(getGame(), modelLoader.getModel(modelType.Car), modelLoader.getModelTextures(modelType.Car), new Path(nodes, normalMap), uid++));
            nodes = new List<Vector3>();
            for (int i = 0; i < 100; i++)
                nodes.Add(new Vector3(hw - i, hh, heightMap.getHeight(hw - i, hh)));
            entities.Add(new MovableEntity(getGame(), modelLoader.getModel(modelType.Car), modelLoader.getModelTextures(modelType.Car), new Path(nodes, normalMap), uid++));
            nodes = new List<Vector3>();
            for (int i = 0; i < 100; i++)
                nodes.Add(new Vector3(hw, hh + i, heightMap.getHeight(hw, hh + i)));
            entities.Add(new MovableEntity(getGame(), modelLoader.getModel(modelType.Car), modelLoader.getModelTextures(modelType.Car), new Path(nodes, normalMap), uid++));
            nodes = new List<Vector3>();
            for (int i = 0; i < 100; i++)
                nodes.Add(new Vector3(hw, hh - i, heightMap.getHeight(hw, hh - i)));
            entities.Add(new MovableEntity(getGame(), modelLoader.getModel(modelType.Car), modelLoader.getModelTextures(modelType.Car), new Path(nodes, normalMap), uid++));
            nodes = new List<Vector3>();
            for (int i = 0; i < 100; i++)
                nodes.Add(new Vector3(hw + i, hh + i, heightMap.getHeight(hw + i, hh + i)));
            entities.Add(new MovableEntity(getGame(), modelLoader.getModel(modelType.Car), modelLoader.getModelTextures(modelType.Car), new Path(nodes, normalMap), uid++));
            nodes = new List<Vector3>();
            for (int i = 0; i < 100; i++)
                nodes.Add(new Vector3(hw - i, hh - i, heightMap.getHeight(hw - i, hh - i)));
            entities.Add(new MovableEntity(getGame(), modelLoader.getModel(modelType.Car), modelLoader.getModelTextures(modelType.Car), new Path(nodes, normalMap), uid++));
            nodes = new List<Vector3>();
            for (int i = 0; i < 100; i++)
                nodes.Add(new Vector3(hw + i, hh - i, heightMap.getHeight(hw + i, hh - i)));
            entities.Add(new MovableEntity(getGame(), modelLoader.getModel(modelType.Car), modelLoader.getModelTextures(modelType.Car), new Path(nodes, normalMap), uid++));
            nodes = new List<Vector3>();
            for (int i = 0; i < 100; i++)
                nodes.Add(new Vector3(hw - i, hh + i, heightMap.getHeight(hw - i, hh + i)));
            entities.Add(new MovableEntity(getGame(), modelLoader.getModel(modelType.Car), modelLoader.getModelTextures(modelType.Car), new Path(nodes, normalMap), uid++));
        }

        public override void loadContent()
        {
            modelEffect = getContentManager().Load<Effect>("EffectFiles/model");

            terrain.loadContent();

            skybox.loadContent(getContentManager(), getGraphics());
        }

        public override void background()
        {
            Console.WriteLine("LevelState in background");
            //throw new Exception("The method or operation is not implemented.");
        }

        public override void foreground()
        {
            Console.WriteLine("LevelState in foreground");
            //throw new Exception("The method or operation is not implemented.");
        }

        public override void update(GameTime gameTime)
        {
            updateInput();

            camera.update(gameTime);
            terrain.update(gameTime);

            for (int i = 0; i < entities.Count; i++)
                entities[i].update();

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

            if (input.isKeyPressed(GameKeys.RESET)) {
                getStateManager().popState();
                return;
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
                    Console.WriteLine("Single Select");
                    Vector3 mousePoint = terrain.projectToTerrain(startClickX, startClickY);
                    float minDist = 5.0f;
                    MovableEntity selected = null;
                    foreach (MovableEntity entity in entities) {
                        entity.setSelected(false);
                        Vector3 dist = mousePoint - entity.getPosition();
                        if (dist.LengthSquared() < minDist) {
                            minDist = dist.LengthSquared();
                            selected = entity;
                        }
                    }
                    if (selected != null) selected.setSelected(true);
                }
                //select a group of units
                else {
                    Console.WriteLine("Multi Select");
                    int topX = Math.Min(startClickX, currClickX);
                    int topY = Math.Min(startClickY, currClickY);
                    int bottomX = Math.Max(startClickX, currClickX);
                    int bottomY = Math.Max(startClickY, currClickY);
                    Rectangle bounds = new Rectangle(topX, topY, bottomX - topX, bottomY - topY);
                    foreach (MovableEntity entity in entities) {
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
                Console.WriteLine("Commanded Units");
                commandCurrent = true;
                foreach (MovableEntity entity in entities) {
                    if (entity.isSelected()) {
                        List<Vector3> newPathList = new List<Vector3>();
                        newPathList.Add(entity.getPath().getRemainingPath()[0]);
                        Vector3 startPos = newPathList[0];
                        Vector3 endPos = terrain.projectToTerrain(input.getMouseX(), input.getMouseY());
                        Vector3 distLeft = endPos - startPos;
                        Vector3 currPos = startPos;
                        int steps = 0;
                        while (distLeft.Length() > 1 && steps < 1000) {
                            Vector3 pleh = new Vector3(distLeft.X, distLeft.Y, distLeft.Z);
                            currPos = currPos + Vector3.Normalize(pleh);
                            currPos.Z = heightMap.getHeight(currPos.X, currPos.Y);
                            newPathList.Add(currPos);
                            distLeft = endPos - currPos;
                            steps++;
                        }
                        newPathList.Add(endPos);

                        Path newPath = new Path(newPathList, normalMap);
                        entity.setPath(newPath);
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
                entities.Add(new MovableEntity(getGame(), modelLoader.getModel(modelType.Car), modelLoader.getModelTextures(modelType.Car), new Path(dummyPath, normalMap), 0));
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
                foreach (MovableEntity entity in entities) {
                    Vector3 dist = mousePoint - entity.getPosition();
                    if (dist.Length() < minDist) {
                        minDist = dist.Length();
                        deleted = entity;
                    }
                }
                if (deleted != null) entities.Remove(deleted);
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

            terrain.render();
            skybox.render();

            for (int i = 0; i < entities.Count; i++)
                entities[i].render(graphics, spriteBatch, camera, modelEffect);

            if (selectCurrent) {
                lineTool.render();
            }
        }
    }
}
