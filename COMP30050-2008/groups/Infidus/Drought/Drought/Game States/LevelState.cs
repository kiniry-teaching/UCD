using System;
using System.Collections.Generic;
using System.Text;
using Drought;
using Drought.State;
using Drought.World;
using Microsoft.Xna.Framework;
using Microsoft.Xna.Framework.Graphics;

namespace Drought.GameStates
{
    class LevelState : GameState 
    {
        Terrain terrain;
        Camera camera; 
        
        HeightMap heightMap;
        TextureMap textureMap;

        public LevelState(IStateManager manager, Game game, string fileName) :
            base(manager, game)
        {
            heightMap = new HeightMap(fileName);
            textureMap = new TextureMap(fileName);

            terrain = new Terrain(getGraphics(), getContentManager(), heightMap, textureMap);

            camera = new Camera(game, heightMap);

            terrain.loadContent();
            terrain.setProjectionMatrix(camera.getProjectionMatrix());
            terrain.setViewMatrix(camera.getViewMatrix());
        }

        public override void loadContent()
        {
            
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
            camera.update(gameTime);
            terrain.setViewMatrix(camera.getViewMatrix());
            terrain.update(gameTime);
        }

        public override void  render(GraphicsDevice graphics, SpriteBatch spriteBatch)
        {
            graphics.RenderState.FillMode = FillMode.Solid;
            graphics.RenderState.CullMode = CullMode.None;
            graphics.Clear(ClearOptions.Target | ClearOptions.DepthBuffer, Color.OrangeRed, 1.0f, 0);

            terrain.render();
        }
    }
}
