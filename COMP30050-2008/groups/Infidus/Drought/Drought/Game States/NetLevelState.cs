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
using Drought.Network;

namespace Drought.GameStates
{
    /** 
     * Branch of LevelState; a testbed for early networking functions,
     * so any broken functionality won't impede others' efforts.
     */
    class NetLevelState : GameState 
    {
        Terrain terrain;
        Camera camera; 
        
        HeightMap heightMap;
        TextureMap textureMap;

        private NormalMap normalMap;

        private DeviceInput input;

        private List<MovableEntity> localEntities;
        private List<MovableEntity> remoteEntities;

        private Model3D truckModel;

        private Model3D xyzModel;

        private NetworkManager networkManager;

        private bool hosting;

        public NetLevelState(IStateManager manager, Game game, string fileName, bool isHost) :
            base(manager, game)
        {
            networkManager = ((Game1)game).getNetworkManager();
            hosting = isHost;

            input = DeviceInput.getInput();
            heightMap = new HeightMap(fileName);
            textureMap = new TextureMap(fileName);

            terrain = new Terrain(getGraphics(), getContentManager(), heightMap, textureMap);

            camera = new Camera(game, heightMap);

            loadContent();

            normalMap = new NormalMap(heightMap);

            localEntities = new List<MovableEntity>();
            int uid = 0;
            List<Vector3> nodes = new List<Vector3>();
            for (int i = 100; i < 200; i++)
                nodes.Add(new Vector3(i, i, heightMap.getHeight(i, i)));
            localEntities.Add(new MovableEntity(truckModel, new Path(nodes, normalMap), uid++));

            nodes = new List<Vector3>();
            for (int i = 100; i < 200; i++)
                nodes.Add(new Vector3(i, 200, heightMap.getHeight(i, 200)));
            localEntities.Add(new MovableEntity(truckModel, new Path(nodes, normalMap), uid++));
            
            nodes = new List<Vector3>();
            for (int i = 100; i < 200; i++)
                nodes.Add(new Vector3(200, i, heightMap.getHeight(200, i)));
            localEntities.Add(new MovableEntity(truckModel, new Path(nodes, normalMap), uid++));

            uid = 0;
            remoteEntities = new List<MovableEntity>();
            nodes = new List<Vector3>();
            for (int i = 100; i > 0; i--)
                nodes.Add(new Vector3(i, i, heightMap.getHeight(i, i)));
            remoteEntities.Add(new MovableEntity(truckModel, new Path(nodes, normalMap), uid++));

            nodes = new List<Vector3>();
            for (int i = 100; i > 0; i--)
                nodes.Add(new Vector3(i, 200, heightMap.getHeight(i, 200)));
            remoteEntities.Add(new MovableEntity(truckModel, new Path(nodes, normalMap), uid++));

            nodes = new List<Vector3>();
            for (int i = 100; i > 0; i--)
                nodes.Add(new Vector3(200, i, heightMap.getHeight(200, i)));
            remoteEntities.Add(new MovableEntity(truckModel, new Path(nodes, normalMap), uid++));
            
            if (hosting) {
                List<MovableEntity> tempList = localEntities;
                localEntities = remoteEntities;
                remoteEntities = tempList;
            }
        }

        public override void loadContent()
        {
            terrain.loadContent();
            terrain.setProjectionMatrix(camera.getProjectionMatrix());
            terrain.setViewMatrix(camera.getViewMatrix());
            truckModel = new Model3D("Models/Truck/truck", camera);
            truckModel.loadContent(getContentManager(), getGraphics());

            xyzModel = new Model3D("Models/xyz", camera);
            xyzModel.loadContent(getContentManager(), getGraphics());
            xyzModel.rotationAngles = new Vector3(0, 0, 0);
            float xyzX = heightMap.getMapWidth() / 2.0f;
            float xyzY = heightMap.getMapHeight() / 2.0f;
            xyzModel.position = new Vector3(xyzX, xyzY, heightMap.getHeight(xyzX, xyzY) + 5.0f);
        }

        public override void background()
        {
            Console.WriteLine("NetLevelState in background");
            //throw new Exception("The method or operation is not implemented.");
        }

        public override void foreground()
        {
            Console.WriteLine("NetLevelState in foreground");
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

            for (int i = 0; i < localEntities.Count; i++)
                localEntities[i].update();

            foreach (MovableEntity entity in localEntities) {
                networkManager.sendPos(entity);
                //Console.WriteLine("sent: " + entity.getPosition());
            }
            
            while (networkManager.hasMoreData()) {
                Vector3 vec = networkManager.recievePos();
                int uid = networkManager.recieveUID();
                //Console.WriteLine("uid: " + uid + " recieved");
                foreach (MovableEntity entity in remoteEntities)
                    if (entity.uniqueID == uid)
                        entity.setPosition(vec);
                //if (vec != new Vector3()) Console.WriteLine("recieved: " + vec);
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

            xyzModel.render(graphics);

            for (int i = 0; i < localEntities.Count; i++)
                localEntities[i].render(graphics);
            for (int i = 0; i < remoteEntities.Count; i++)
                remoteEntities[i].render(graphics);
        }
    }
}
