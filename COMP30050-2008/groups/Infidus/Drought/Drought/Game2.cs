using System;
using System.Collections.Generic;
using Microsoft.Xna.Framework;
using Microsoft.Xna.Framework.Audio;
using Microsoft.Xna.Framework.Content;
using Microsoft.Xna.Framework.GamerServices;
using Microsoft.Xna.Framework.Graphics;
using Microsoft.Xna.Framework.Input;
using Microsoft.Xna.Framework.Net;
using Microsoft.Xna.Framework.Storage;
using Drought.GameStates;

namespace Drought
{

    public class Game2 : Microsoft.Xna.Framework.Game
    {
        GraphicsDeviceManager graphics;
        SpriteBatch spriteBatch;

        LevelState l;

        public Game2()
        {
            graphics = new GraphicsDeviceManager(this);
            Content.RootDirectory = "Content";
        }


        
        
        protected override void Initialize()
        {
            graphics.PreferredBackBufferWidth = 800;
            graphics.PreferredBackBufferHeight = 600;
            graphics.ApplyChanges();

            l = new LevelState(null, this, "level_0");

            base.Initialize();
        }


        
        
        protected override void LoadContent()
        {
            
            spriteBatch = new SpriteBatch(GraphicsDevice);

            l.loadContent();
        }


        
        
        protected override void UnloadContent()
        {
            // TODO: Unload any non ContentManager content here
        }


        
        
        protected override void Update(GameTime gameTime)
        {
            if (GamePad.GetState(PlayerIndex.One).Buttons.Back == ButtonState.Pressed)
                this.Exit();

            l.update(gameTime);

            base.Update(gameTime);
        }



        protected override void Draw(GameTime gameTime)
        {
            
            l.render(graphics.GraphicsDevice, spriteBatch);

            base.Draw(gameTime);
        }

        public GraphicsDevice getGraphics()
        {
            return graphics.GraphicsDevice;
        }

        public SpriteBatch getSpriteBatch()
        {
            return spriteBatch;
        }
    }
}
