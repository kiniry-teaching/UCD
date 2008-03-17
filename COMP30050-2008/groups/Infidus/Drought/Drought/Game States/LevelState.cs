using System;
using System.Collections.Generic;
using System.Text;
using Drought;
using Drought.State;
using Drought.World;
using Microsoft.Xna.Framework;
using Microsoft.Xna.Framework.Graphics;
using Drought.Entity;
using Drought.Input;
using Drought.Graphics;

namespace Drought.GameStates
{
    class LevelState : GameState 
    {
        Terrain terrain;
        Camera camera; 
        
        HeightMap heightMap;
        TextureMap textureMap;

        private NormalMap normalMap;

        private DeviceInput input;

        private List<MovableEntity> entities;

        private Model3D truckModel;

        private Model3D xyzModel;

        public LevelState(IStateManager manager, Game game, string fileName) :
            base(manager, game)
        {
            input = DeviceInput.getInput();
            heightMap = new HeightMap(fileName);
            textureMap = new TextureMap(fileName);

            terrain = new Terrain(getGraphics(), getContentManager(), heightMap, textureMap);

            camera = new Camera(game, heightMap);

            loadContent();

            normalMap = new NormalMap(heightMap);

            //testing entity here
            entities = new List<MovableEntity>();
            List<Vector3> nodes = new List<Vector3>();
            for(int i = 0; i < 100; i++)
                nodes.Add(new Vector3(i, i, heightMap.getHeight(i, i)));
            entities.Add(new MovableEntity(truckModel, new Path(nodes, normalMap)));
            
            nodes = new List<Vector3>();
            for (int i = 0; i < 100; i++)
                nodes.Add(new Vector3(i, 100, heightMap.getHeight(i, 100)));
            entities.Add(new MovableEntity(truckModel, new Path(nodes, normalMap)));

            nodes = new List<Vector3>();
            for (int i = 0; i < 100; i++)
                nodes.Add(new Vector3(0, i, heightMap.getHeight(0, i)));
            entities.Add(new MovableEntity(truckModel, new Path(nodes, normalMap)));
            
            int hw = heightMap.getMapWidth() / 2;
            int hh = heightMap.getMapHeight() / 2;
            nodes = new List<Vector3>();
            for (int i = 0; i < 100; i++)
                nodes.Add(new Vector3(hw + i, hh, heightMap.getHeight(hw + i, hh)));
            entities.Add(new MovableEntity(truckModel, new Path(nodes, normalMap)));
            nodes = new List<Vector3>();
            for (int i = 0; i < 100; i++)
                nodes.Add(new Vector3(hw - i, hh, heightMap.getHeight(hw - i, hh)));
            entities.Add(new MovableEntity(truckModel, new Path(nodes, normalMap)));
            nodes = new List<Vector3>();
            for (int i = 0; i < 100; i++)
                nodes.Add(new Vector3(hw, hh + i, heightMap.getHeight(hw, hh + i)));
            entities.Add(new MovableEntity(truckModel, new Path(nodes, normalMap)));
            nodes = new List<Vector3>();
            for (int i = 0; i < 100; i++)
                nodes.Add(new Vector3(hw, hh - i, heightMap.getHeight(hw, hh - i)));
            entities.Add(new MovableEntity(truckModel, new Path(nodes, normalMap)));
            nodes = new List<Vector3>();
            for (int i = 0; i < 100; i++)
                nodes.Add(new Vector3(hw + i, hh + i, heightMap.getHeight(hw + i, hh + i)));
            entities.Add(new MovableEntity(truckModel, new Path(nodes, normalMap)));
            nodes = new List<Vector3>();
            for (int i = 0; i < 100; i++)
                nodes.Add(new Vector3(hw - i, hh - i, heightMap.getHeight(hw - i, hh - i)));
            entities.Add(new MovableEntity(truckModel, new Path(nodes, normalMap)));
            nodes = new List<Vector3>();
            for (int i = 0; i < 100; i++)
                nodes.Add(new Vector3(hw + i, hh - i, heightMap.getHeight(hw + i, hh - i)));
            entities.Add(new MovableEntity(truckModel, new Path(nodes, normalMap)));
            nodes = new List<Vector3>();
            for (int i = 0; i < 100; i++)
                nodes.Add(new Vector3(hw - i, hh + i, heightMap.getHeight(hw - i, hh + i)));
            entities.Add(new MovableEntity(truckModel, new Path(nodes, normalMap)));
            
        }

        public override void loadContent()
        {
            terrain.loadContent();
            terrain.setProjectionMatrix(camera.getProjectionMatrix());
            terrain.setViewMatrix(camera.getViewMatrix());
            truckModel = new Model3D("Models/xyz", camera);
            truckModel.loadContent(getContentManager(), getGraphics());

            xyzModel = new Model3D("Models/Truck/truck", camera);
            xyzModel.loadContent(getContentManager(), getGraphics());
            xyzModel.rotationAngles = new Vector3(0, 0, 0);
            float xyzX = heightMap.getMapWidth() / 2.0f;
            float xyzY = heightMap.getMapHeight() / 2.0f;
            xyzModel.position = new Vector3(xyzX, xyzY, heightMap.getHeight(xyzX, xyzY) + 5.0f);
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
            
            camera.update(gameTime);
            terrain.setViewMatrix(camera.getViewMatrix());
            terrain.update(gameTime);

            for (int i = 0; i < entities.Count; i++)
                entities[i].update();
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

            xyzModel.render(graphics);

            for (int i = 0; i < entities.Count; i++)
                entities[i].render(graphics);
        }
    }
}
