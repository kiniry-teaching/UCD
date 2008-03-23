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

        private bool clickCurrent;
        private bool rightClickCurrent;

        private int startClickX, startClickY;
        private int currClickX, currClickY;

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

            terrain = new Terrain(getGraphics(), getContentManager(), heightMap, textureMap);
            camera = new Camera(game, heightMap);

            skybox = new Skybox(camera);

            modelLoader = new ModelLoader(game.Content, game.getGraphics());

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
            entities.Add(new MovableEntity(getGame(), camera, modelLoader.getModel(modelType.Car), modelLoader.getModelTextures(modelType.Car), new Path(nodes, normalMap), uid++));
            nodes = new List<Vector3>();
            for (int i = 0; i < 100; i++)
                nodes.Add(new Vector3(hw - i, hh, heightMap.getHeight(hw - i, hh)));
            entities.Add(new MovableEntity(getGame(), camera, modelLoader.getModel(modelType.Car), modelLoader.getModelTextures(modelType.Car), new Path(nodes, normalMap), uid++));
            nodes = new List<Vector3>();
            for (int i = 0; i < 100; i++)
                nodes.Add(new Vector3(hw, hh + i, heightMap.getHeight(hw, hh + i)));
            entities.Add(new MovableEntity(getGame(), camera, modelLoader.getModel(modelType.Car), modelLoader.getModelTextures(modelType.Car), new Path(nodes, normalMap), uid++));
            nodes = new List<Vector3>();
            for (int i = 0; i < 100; i++)
                nodes.Add(new Vector3(hw, hh - i, heightMap.getHeight(hw, hh - i)));
            entities.Add(new MovableEntity(getGame(), camera, modelLoader.getModel(modelType.Car), modelLoader.getModelTextures(modelType.Car), new Path(nodes, normalMap), uid++));
            nodes = new List<Vector3>();
            for (int i = 0; i < 100; i++)
                nodes.Add(new Vector3(hw + i, hh + i, heightMap.getHeight(hw + i, hh + i)));
            entities.Add(new MovableEntity(getGame(), camera, modelLoader.getModel(modelType.Car), modelLoader.getModelTextures(modelType.Car), new Path(nodes, normalMap), uid++));
            nodes = new List<Vector3>();
            for (int i = 0; i < 100; i++)
                nodes.Add(new Vector3(hw - i, hh - i, heightMap.getHeight(hw - i, hh - i)));
            entities.Add(new MovableEntity(getGame(), camera, modelLoader.getModel(modelType.Car), modelLoader.getModelTextures(modelType.Car), new Path(nodes, normalMap), uid++));
            nodes = new List<Vector3>();
            for (int i = 0; i < 100; i++)
                nodes.Add(new Vector3(hw + i, hh - i, heightMap.getHeight(hw + i, hh - i)));
            entities.Add(new MovableEntity(getGame(), camera, modelLoader.getModel(modelType.Car), modelLoader.getModelTextures(modelType.Car), new Path(nodes, normalMap), uid++));
            nodes = new List<Vector3>();
            for (int i = 0; i < 100; i++)
                nodes.Add(new Vector3(hw - i, hh + i, heightMap.getHeight(hw - i, hh + i)));
            entities.Add(new MovableEntity(getGame(), camera, modelLoader.getModel(modelType.Car), modelLoader.getModelTextures(modelType.Car), new Path(nodes, normalMap), uid++));
        }

        public override void loadContent()
        {
            modelEffect = getContentManager().Load<Effect>("EffectFiles/model");

            terrain.loadContent();
            terrain.setProjectionMatrix(camera.getProjectionMatrix());
            terrain.setViewMatrix(camera.getViewMatrix());

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
            {
                camera.zoomIn();
                waterMap.addWater(1);
            }
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

            camera.update(gameTime);
            terrain.setViewMatrix(camera.getViewMatrix());
            terrain.update(gameTime);

            for (int i = 0; i < entities.Count; i++)
                entities[i].update();

            /* Selecting Units */
            if (!clickCurrent && input.isKeyPressed(GameKeys.MOUSE_CLICK)) {
                clickCurrent = true;
                startClickX = input.getMouseX();
                startClickY = input.getMouseY();
            }
            else if (clickCurrent && !input.isKeyPressed(GameKeys.MOUSE_CLICK)) {
                clickCurrent = false;
                currClickX = input.getMouseX();
                currClickY = input.getMouseY();
                int topX = Math.Min(startClickX, currClickX);
                int topY = Math.Min(startClickY, currClickY);
                int bottomX = Math.Max(startClickX, currClickX);
                int bottomY = Math.Max(startClickY, currClickY);
                Rectangle bounds = new Rectangle(topX, topY, bottomX - topX, bottomY - topY);
                foreach (MovableEntity entity in entities) {
                    entity.setSelected(false);
                    Vector3 entityPos = getGraphics().Viewport.Project(entity.getPosition(), camera.getProjectionMatrix(), camera.getViewMatrix(), Matrix.Identity);
                    if (entityPos.Z < 1) {
                        if (bounds.Contains(new Point((int)entityPos.X, (int)entityPos.Y))) {
                            entity.setSelected(true);
                        }
                    }
                }
            }
            if (clickCurrent) {
                currClickX = input.getMouseX();
                currClickY = input.getMouseY();
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

            /* Commanding Units */
            if (!rightClickCurrent && input.isKeyPressed(GameKeys.MOUSE_RIGHT_CLICK)) {
                rightClickCurrent = true;
                foreach (MovableEntity entity in entities) {
                    if (entity.isSelected()) {
                        List<Vector3> newPathList = new List<Vector3>();
                        newPathList.Add(entity.getPath().getRemainingPath()[0]);
                        Vector3 startPos = newPathList[0];
                        Vector3 endPos = terrain.projectToTerrain(getGraphics(), camera, input.getMouseX(), input.getMouseY());
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
            else if (rightClickCurrent && !input.isKeyPressed(GameKeys.MOUSE_RIGHT_CLICK)) {
                rightClickCurrent = false;
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

            if (clickCurrent) {
                lineTool.render();
            }
        }
    }
}
