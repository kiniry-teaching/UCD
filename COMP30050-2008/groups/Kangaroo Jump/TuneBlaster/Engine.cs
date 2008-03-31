
#region Using Statements
using System;
using System.Collections.Generic;
using Microsoft.Xna.Framework;
using Microsoft.Xna.Framework.Audio;
using Microsoft.Xna.Framework.Content;
using Microsoft.Xna.Framework.Graphics;
using Microsoft.Xna.Framework.Input;
using Microsoft.Xna.Framework.Storage;
using TuneBlaster_.Graphics;
#endregion

namespace TuneBlaster_
{
    /// <summary>
    /// The Class that calls everything
    /// Defalt Class
    /// Authors Hugh Corrigan, Ahmed Warreth, Dermot Kirby
    /// </summary>
    /// 



    public class Engine : Microsoft.Xna.Framework.Game
    {
        
        GraphicsDeviceManager graphics;
        ContentManager content;
        public SpriteBatch spriteBatch;

        // a random number generator 
        public static Random Random = new Random();
        

        Texture2D texture;
        Core core;
        BallManager ball;
        Image background;
        GameAudio music;
        GamePadState gamePadState = GamePad.GetState(PlayerIndex.One);
        public static ExplosionParticleSystem explosion;
        public static ExplosionSmokeParticleSystem smoke;
        public static RedParticle redblast;
        public static GreenParticle greenblast;
        public static BlueParticle blueblast;
        public static PurpleParticle purpleblast;
        Image.value colour;

        public Engine()
        {

            graphics = new GraphicsDeviceManager(this);
            content = new ContentManager(Services);
            core = new Core();
            ball = new BallManager(core, this);
            background = new Image();
            music = new GameAudio();

            this.graphics.PreferredBackBufferWidth = 800;
            this.graphics.PreferredBackBufferHeight = 600;
            explosion = new ExplosionParticleSystem(this,1);
            Components.Add(explosion);
            smoke = new ExplosionSmokeParticleSystem(this, 2);
            Components.Add(smoke);
            blueblast = new BlueParticle(this,1);
            Components.Add(blueblast);
            redblast = new RedParticle(this,1);
            Components.Add(redblast);
            greenblast = new GreenParticle(this, 1);
            Components.Add(greenblast);
            purpleblast = new PurpleParticle(this, 1);
            Components.Add(purpleblast);

            //this.graphics.IsFullScreen = true;
        }



        // gives a random float between two values
        public static float RandomBetween(float min, float max)
        {
            return min + (float)Random.NextDouble() * (max - min);
        }





        /// <summary>
        /// Allows the game to perform any initialization it needs to before starting to run.
        /// This is where it can query for any required services and load any non-graphic
        /// related content.  Calling base.Initialize will enumerate through any components
        /// and initialize them as well.
        /// </summary>
        protected override void Initialize()
        {
            core.Initialise(new Vector2(150f, 150f), new Vector2(400f,300f), this);
            background.Initialise(new Vector2(1200, 800), new Vector2(600,400), this);
            ball.Initialise();
            base.Initialize();
            music.Initialise();
            //Content.RootDirectory = "Content";
        }


        /// <summary>
        /// Load your graphics content.  If loadAllContent is true, you should
        /// load content from both ResourceManagementMode pools.  Otherwise, just
        /// load ResourceManagementMode.Manual content.
        /// </summary>
        /// <param name="loadAllContent">Which type of content to load.</param>
        protected override void LoadGraphicsContent(bool loadAllContent)
        {
            if (loadAllContent)
            {
                spriteBatch = new SpriteBatch(graphics.GraphicsDevice);
                texture = content.Load<Texture2D>(@"Resources\Textures\space-background");
                background.LoadGraphicsContent(spriteBatch, texture);
                texture = content.Load<Texture2D>(@"Resources\Textures\Core");
                core.LoadGraphicsContent(spriteBatch, texture);
                ball.LoadGraphicsContent(spriteBatch);
                // TODO: Load any ResourceManagementMode.Automatic content
            }

            // TODO: Load any ResourceManagementMode.Manual content
        }



      



        /// <summary>
        /// Unload your graphics content.  If unloadAllContent is true, you should
        /// unload content from both ResourceManagementMode pools.  Otherwise, just
        /// unload ResourceManagementMode.Manual content.  Manual content will get
        /// Disposed by the GraphicsDevice during a Reset.
        /// </summary>
        /// <param name="unloadAllContent">Which type of content to unload.</param>
        protected override void UnloadGraphicsContent(bool unloadAllContent)
        {
            if (unloadAllContent == true)
            {
                content.Unload();
            }
        }


        /// <summary>
        /// Allows the game to run logic such as updating the world,
        /// checking for collisions, gathering input and playing audio.
        /// </summary>
        /// <param name="gameTime">Provides a snapshot of timing values.</param>
        protected override void Update(GameTime gameTime)
        {
            // Allows the default game to exit on Xbox 360 and Windows
            if (GamePad.GetState(PlayerIndex.One).Buttons.Back == ButtonState.Pressed)
                this.Exit();

           colour = core.Update(gameTime, Keyboard.GetState(), GamePad.GetState(PlayerIndex.One));

           if (colour == Image.value.green)
               music.InstrChanger(Image.value.green);

           /* if (colour == Image.value.blue)
               music.InstrChanger(Image.value.blue); */

           if (colour == Image.value.red)
               music.InstrChanger(Image.value.red);

           if (colour == Image.value.purple)
               music.InstrChanger(Image.value.purple);

           ball.Update(gameTime);
           music.UpdateAudio();
           base.Update(gameTime);
        }


        /// <summary>
        /// This is called when the game should draw itself.
        /// </summary>
        /// <param name="gameTime">Provides a snapshot of timing values.</param>
        protected override void Draw(GameTime gameTime)
        {
            graphics.GraphicsDevice.Clear(Color.Black);
            spriteBatch.Begin();
            background.Draw(gameTime);
            core.Draw(gameTime);
            ball.Draw(gameTime);
            spriteBatch.End();

            base.Draw(gameTime);
        }
    }
}
