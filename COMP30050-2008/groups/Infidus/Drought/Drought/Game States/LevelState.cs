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
        private Terrain terrain;
        
        private Camera camera; 
        
        private HeightMap heightMap;

        private TextureMap textureMap;

        private WaterMap waterMap;

        private NormalMap normalMap;

        private DeviceInput input;

        private List<MovableEntity> entities;

        private Effect modelEffect;

        private enum modelIndexes { Skybox, XYZ, Truck, Car };

        private Model[] models;

        private Dictionary<int,Texture2D[]> modelTextures;

        public LevelState(IStateManager manager, Game game, string fileName) :
            base(manager, game)
        {
            input = DeviceInput.getInput();
            heightMap = new HeightMap(fileName);
            textureMap = new TextureMap(fileName);
            waterMap = new WaterMap(heightMap, textureMap);

            terrain = new Terrain(getGraphics(), getContentManager(), heightMap, textureMap);

            camera = new Camera(game, heightMap);

            models = new Model[4];
            modelTextures = new Dictionary<int, Texture2D[]>();

            loadContent();

            normalMap = new NormalMap(heightMap);

            //testing entity here
            entities = new List<MovableEntity>();
            List<Vector3> nodes = new List<Vector3>();
            for(int i = 0; i < 100; i++)
                nodes.Add(new Vector3(i, i, heightMap.getHeight(i, i)));
//            entities.Add(new MovableEntity(models[(int)modelIndexes.Car], modelTextures[(int)modelIndexes.Car], new Path(nodes, normalMap), 0));
            
            nodes = new List<Vector3>();
            for (int i = 0; i < 100; i++)
                nodes.Add(new Vector3(i, 100, heightMap.getHeight(i, 100)));
//            entities.Add(new MovableEntity(models[(int)modelIndexes.Truck], modelTextures[(int)modelIndexes.Truck], new Path(nodes, normalMap), 1));

            nodes = new List<Vector3>();
            for (int i = 0; i < 100; i++)
                nodes.Add(new Vector3(0, i, heightMap.getHeight(0, i)));
//            entities.Add(new MovableEntity(models[(int)modelIndexes.XYZ], modelTextures[(int)modelIndexes.XYZ], new Path(nodes, normalMap), 2));

            nodes = new List<Vector3>();
            for (int i = 0; i < 100; i++)
                nodes.Add(new Vector3(0, i, heightMap.getHeight(0, i)));
//            entities.Add(new MovableEntity(models[(int)modelIndexes.Skybox], modelTextures[(int)modelIndexes.Skybox], new Path(nodes, normalMap), 2));




            
            int hw = heightMap.getMapWidth() / 2;
            int hh = heightMap.getMapHeight() / 2;
            nodes = new List<Vector3>();
            for (int i = 0; i < 100; i++)
                nodes.Add(new Vector3(hw + i, hh, heightMap.getHeight(hw + i, hh)));
            //entities.Add(new MovableEntity(truckModel, new Path(nodes, normalMap)));
            nodes = new List<Vector3>();
            for (int i = 0; i < 100; i++)
                nodes.Add(new Vector3(hw - i, hh, heightMap.getHeight(hw - i, hh)));
            //entities.Add(new MovableEntity(truckModel, new Path(nodes, normalMap)));
            nodes = new List<Vector3>();
            for (int i = 0; i < 100; i++)
                nodes.Add(new Vector3(hw, hh + i, heightMap.getHeight(hw, hh + i)));
            //entities.Add(new MovableEntity(truckModel, new Path(nodes, normalMap)));
            nodes = new List<Vector3>();
            for (int i = 0; i < 100; i++)
                nodes.Add(new Vector3(hw, hh - i, heightMap.getHeight(hw, hh - i)));
            //entities.Add(new MovableEntity(truckModel, new Path(nodes, normalMap)));
            nodes = new List<Vector3>();
            for (int i = 0; i < 100; i++)
                nodes.Add(new Vector3(hw + i, hh + i, heightMap.getHeight(hw + i, hh + i)));
            //entities.Add(new MovableEntity(truckModel, new Path(nodes, normalMap)));
            nodes = new List<Vector3>();
            for (int i = 0; i < 100; i++)
                nodes.Add(new Vector3(hw - i, hh - i, heightMap.getHeight(hw - i, hh - i)));
            //entities.Add(new MovableEntity(truckModel, new Path(nodes, normalMap)));
            nodes = new List<Vector3>();
            for (int i = 0; i < 100; i++)
                nodes.Add(new Vector3(hw + i, hh - i, heightMap.getHeight(hw + i, hh - i)));
            //entities.Add(new MovableEntity(truckModel, new Path(nodes, normalMap)));
            nodes = new List<Vector3>();
            for (int i = 0; i < 100; i++)
                nodes.Add(new Vector3(hw - i, hh + i, heightMap.getHeight(hw - i, hh + i)));
            //entities.Add(new MovableEntity(truckModel, new Path(nodes, normalMap)));
            
        }

        public override void loadContent()
        {
            modelEffect = getContentManager().Load<Effect>("EffectFiles/model");

            //initialise models
            models[(int)modelIndexes.Truck] = getContentManager().Load<Model>("Models/Truck/truck");
            models[(int)modelIndexes.XYZ] = getContentManager().Load<Model>("Models/xyz");
            models[(int)modelIndexes.Car] = getContentManager().Load<Model>("Models/Car/car");
            models[(int)modelIndexes.Skybox] = getContentManager().Load<Model>("Models/Skybox/skybox");

            for(int index = 0; index < models.Length; index++)
            {
                Model model = models[index];

                int textureCount = 0;
                foreach (ModelMesh mesh in model.Meshes)
                    textureCount += mesh.Effects.Count;

                Texture2D[] textures = new Texture2D[textureCount];

                int i = 0;
                foreach (ModelMesh mesh in model.Meshes)
                    foreach (BasicEffect basicEffect in mesh.Effects)
                        textures[i++]  = basicEffect.Texture;

                modelTextures.Add(index, textures);

                foreach (ModelMesh mesh in model.Meshes)
                    foreach (ModelMeshPart meshPart in mesh.MeshParts)
                        meshPart.Effect = modelEffect.Clone(getGraphics());
            }

            terrain.loadContent();
            terrain.setProjectionMatrix(camera.getProjectionMatrix());
            terrain.setViewMatrix(camera.getViewMatrix());

            
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

            for (int i = 0; i < entities.Count; i++)
                entities[i].render(graphics, camera, modelEffect);
        }
    }
}
