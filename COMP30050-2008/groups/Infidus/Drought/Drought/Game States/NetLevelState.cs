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
using Drought.Network;

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

        private Camera camera;

        private HeightMap heightMap;

        private TextureMap textureMap;

        private WaterMap waterMap;

        private NormalMap normalMap;

        private DeviceInput input;

        private Effect modelEffect;

        private Dictionary<int, Texture2D[]> modelTextures;

        private enum modelIndexes { Skybox, XYZ, Truck, Car };

        private Model[] models;

        private List<MovableEntity> localEntities;

        private List<MovableEntity> remoteEntities;

        private NetworkManager networkManager;

        private bool hosting;

        private Texture2D selector;

        private bool clickCurrent;

        private int startClickX, startClickY;
        private int currClickX, currClickY;

        BasicEffect basicEffect;

        VertexDeclaration vertexDeclaration;
        VertexPositionNormalTexture[] pointList;
        VertexBuffer vertexBuffer;

        IndexBuffer lineStripIndexBuffer;

        public NetLevelState(IStateManager manager, DroughtGame game, string fileName, bool isHost) :
            base(manager, game)
        {
            networkManager = game.getNetworkManager();
            hosting = isHost;

            input = DeviceInput.getInput();
            heightMap = new HeightMap(fileName);
            textureMap = new TextureMap(fileName);

            terrain = new Terrain(getGraphics(), getContentManager(), heightMap, textureMap);

            camera = new Camera(game, heightMap);

            skybox = new Skybox(camera);

            models = new Model[4];
            modelTextures = new Dictionary<int, Texture2D[]>();

            loadContent();

            normalMap = new NormalMap(heightMap);

            localEntities = new List<MovableEntity>();
            int uid = 0;
            List<Vector3> nodes = new List<Vector3>();
            for (int i = 100; i < 200; i++)
                nodes.Add(new Vector3(i, i, heightMap.getHeight(i, i)));
            localEntities.Add(new MovableEntity(models[(int)modelIndexes.Car], modelTextures[(int)modelIndexes.Car], selector, new Path(nodes, normalMap), uid++));

            nodes = new List<Vector3>();
            for (int i = 100; i < 200; i++)
                nodes.Add(new Vector3(i, 200, heightMap.getHeight(i, 200)));
            localEntities.Add(new MovableEntity(models[(int)modelIndexes.Car], modelTextures[(int)modelIndexes.Car], selector, new Path(nodes, normalMap), uid++));
            
            nodes = new List<Vector3>();
            for (int i = 100; i < 200; i++)
                nodes.Add(new Vector3(200, i, heightMap.getHeight(200, i)));
            localEntities.Add(new MovableEntity(models[(int)modelIndexes.Car], modelTextures[(int)modelIndexes.Car], selector, new Path(nodes, normalMap), uid++));

            uid = 0;
            remoteEntities = new List<MovableEntity>();
            nodes = new List<Vector3>();
            for (int i = 100; i > 0; i--)
                nodes.Add(new Vector3(i, i, heightMap.getHeight(i, i)));
            remoteEntities.Add(new MovableEntity(models[(int)modelIndexes.Car], modelTextures[(int)modelIndexes.Car], selector, new Path(nodes, normalMap), uid++));

            nodes = new List<Vector3>();
            for (int i = 100; i > 0; i--)
                nodes.Add(new Vector3(i, 200, heightMap.getHeight(i, 200)));
            remoteEntities.Add(new MovableEntity(models[(int)modelIndexes.Car], modelTextures[(int)modelIndexes.Car], selector, new Path(nodes, normalMap), uid++));

            nodes = new List<Vector3>();
            for (int i = 100; i > 0; i--)
                nodes.Add(new Vector3(200, i, heightMap.getHeight(200, i)));
            remoteEntities.Add(new MovableEntity(models[(int)modelIndexes.Car], modelTextures[(int)modelIndexes.Car], selector, new Path(nodes, normalMap), uid++));
            
            if (hosting) {
                List<MovableEntity> tempList = localEntities;
                localEntities = remoteEntities;
                remoteEntities = tempList;
            }

            foreach (MovableEntity entity in localEntities) {
                entity.setSelected(true);
            }

            vertexDeclaration = new VertexDeclaration(getGraphics(), VertexPositionNormalTexture.VertexElements);

            pointList = new VertexPositionNormalTexture[5];
            basicEffect = new BasicEffect(getGraphics(), null);
            basicEffect.DiffuseColor = new Vector3(1.0f, 1.0f, 1.0f);
        }

        public override void loadContent()
        {
            modelEffect = getContentManager().Load<Effect>("EffectFiles/model");

            //initialise models
            models[(int)modelIndexes.Truck] = getContentManager().Load<Model>("Models/Truck/truck");
            models[(int)modelIndexes.XYZ] = getContentManager().Load<Model>("Models/xyz");
            models[(int)modelIndexes.Car] = getContentManager().Load<Model>("Models/Car/car");
            models[(int)modelIndexes.Skybox] = getContentManager().Load<Model>("Models/Skybox/skybox");

            terrain.loadContent();
            terrain.setProjectionMatrix(camera.getProjectionMatrix());
            terrain.setViewMatrix(camera.getViewMatrix());

            skybox.loadContent(getContentManager(), getGraphics());

            for (int index = 0; index < models.Length; index++) {
                Model model = models[index];

                int textureCount = 0;
                foreach (ModelMesh mesh in model.Meshes)
                    textureCount += mesh.Effects.Count;

                Texture2D[] textures = new Texture2D[textureCount];

                int i = 0;
                foreach (ModelMesh mesh in model.Meshes)
                    foreach (BasicEffect basicEffect in mesh.Effects)
                        textures[i++] = basicEffect.Texture;

                modelTextures.Add(index, textures);

                foreach (ModelMesh mesh in model.Meshes)
                    foreach (ModelMeshPart meshPart in mesh.MeshParts)
                        meshPart.Effect = modelEffect.Clone(getGraphics());
            }

            selector = getContentManager().Load<Texture2D>("Textures/selector");
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

            /* Selecting units */
            if (!clickCurrent && input.isKeyPressed(GameKeys.MOUSE_CLICK)) {
                clickCurrent = true;
                startClickX = input.getMouseX();
                startClickY = input.getMouseY();
                currClickX = startClickX;
                currClickY = startClickY;
                UpdatePointsList();
                //Console.WriteLine("started bounding");
            }
            else if (clickCurrent && !input.isKeyPressed(GameKeys.MOUSE_CLICK)) {
                clickCurrent = false;
                Rectangle bounds = new Rectangle(startClickX, startClickY, input.getMouseX() - startClickX, input.getMouseY() - startClickY);
                foreach (MovableEntity entity in localEntities) {
                    entity.setSelected(false);
                    Vector3 v3 = getGraphics().Viewport.Project(entity.getPosition(), camera.getProjectionMatrix(), camera.getViewMatrix(), Matrix.Identity);
                    if (v3.Z < 1) {
                        if (bounds.Contains(new Point((int)v3.X, (int)v3.Y))) {
                            entity.setSelected(true);
                        }
                    }
                }
                //Console.WriteLine("ended bounding");
            }
            else if (clickCurrent) {
                currClickX = input.getMouseX();
                currClickY = input.getMouseY();
                UpdatePointsList();
            }
        }

        private void UpdatePointsList() {
            int screenX = getGraphics().Viewport.Width / 2;
            int screenY = getGraphics().Viewport.Height / 2;
            pointList[0] = new VertexPositionNormalTexture(new Vector3((startClickX - screenX) / (float)screenX, -(startClickY - screenY) / (float)screenY, 0), Vector3.Forward, new Vector2());
            pointList[1] = new VertexPositionNormalTexture(new Vector3((currClickX - screenX) / (float)screenX, -(startClickY - screenY) / (float)screenY, 0), Vector3.Forward, new Vector2());
            pointList[2] = new VertexPositionNormalTexture(new Vector3((currClickX - screenX) / (float)screenX, -(currClickY - screenY) / (float)screenY, 0), Vector3.Forward, new Vector2());
            pointList[3] = new VertexPositionNormalTexture(new Vector3((startClickX - screenX) / (float)screenX, -(currClickY - screenY) / (float)screenY, 0), Vector3.Forward, new Vector2());
            pointList[4] = new VertexPositionNormalTexture(new Vector3((startClickX - screenX) / (float)screenX, -(startClickY - screenY) / (float)screenY, 0), Vector3.Forward, new Vector2());

            vertexBuffer = new VertexBuffer(getGraphics(), VertexPositionNormalTexture.SizeInBytes * (pointList.Length), BufferUsage.None);
            vertexBuffer.SetData<VertexPositionNormalTexture>(pointList);
            short[] lineStripIndices = new short[5];

            for (int i = 0; i < 4; i++)
                lineStripIndices[i] = (short)(i + 1);

            lineStripIndices[4] = 1;
            lineStripIndexBuffer = new IndexBuffer(getGraphics(), sizeof(short) * lineStripIndices.Length, BufferUsage.None, IndexElementSize.SixteenBits);
            lineStripIndexBuffer.SetData<short>(lineStripIndices);
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

            for (int i = 0; i < localEntities.Count; i++)
                localEntities[i].render(graphics, spriteBatch, camera, modelEffect);
            for (int i = 0; i < remoteEntities.Count; i++)
                remoteEntities[i].render(graphics, spriteBatch, camera, modelEffect);

            if (clickCurrent) {

                graphics.VertexDeclaration = vertexDeclaration;

                basicEffect.Begin();
                foreach (EffectPass pass in basicEffect.CurrentTechnique.Passes) {
                    pass.Begin();

                    if (clickCurrent) {
                        graphics.Vertices[0].SetSource(vertexBuffer, 0, VertexPositionNormalTexture.SizeInBytes);

                        graphics.Indices = lineStripIndexBuffer;

                        graphics.DrawIndexedPrimitives(
                            PrimitiveType.LineStrip,
                            0, // vertex buffer offset to add to each element of the index buffer
                            0, // minimum vertex index
                            5, // number of vertices
                            0, // first index element to read
                            4);// number of primitives to draw
                    }

                    pass.End();
                }
                basicEffect.End();
            }
        }
    }
}
