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
using Drought.Menu;
using Drought.Input;
using Drought.GameStates;
using Drought.Network;

namespace Drought
{
    /// <summary>
    /// This is the main type for your game
    /// </summary>
    class Game1 : Microsoft.Xna.Framework.Game
    {
        GraphicsDeviceManager graphics;
        SpriteBatch spriteBatch;
        GameManager gameManager;
        NetworkManager networkManager;

        /**
         * So we can turn it off for testing, since it takes so damn long to start up.
         * NOTE: Only prevents the Gamer Services component from being initialized; if
         * a game tries to host or join a game, nasty exceptions will ensue.
         */
        public static readonly bool NETWORKED = true;

        public Game1()
        {
            graphics = new GraphicsDeviceManager(this);
            Content.RootDirectory = "Content";
            if (NETWORKED) {
                Components.Add(new GamerServicesComponent(this));
            }
            gameManager = new GameManager(this);
            networkManager = NetworkManager.getInstance();
        }

        /// <summary>
        /// Allows the game to perform any initialization it needs to before starting to run.
        /// This is where it can query for any required services and load any non-graphic
        /// related content.  Calling base.Initialize will enumerate through any components
        /// and initialize them as well.
        /// </summary>
        protected override void Initialize()
        {
            graphics.PreferredBackBufferWidth = 800;
            graphics.PreferredBackBufferHeight = 600;
            //graphics.PreferredBackBufferWidth = 1280;
            //graphics.PreferredBackBufferHeight = 800;
            //graphics.PreferredBackBufferWidth = 1650;
            //graphics.PreferredBackBufferHeight = 1080;
            graphics.ApplyChanges();

            DeviceInput input = DeviceInput.getInput();
            input.bind(GameKeys.CHANGE_STATE, Keys.C, ModifierKeys.NONE);
            input.bind(GameKeys.MENU_NEXT, Keys.Down, ModifierKeys.NONE);
            input.bind(GameKeys.MENU_PREV, Keys.Up, ModifierKeys.NONE);
            input.bind(GameKeys.MENU_PRESS, Keys.Enter, ModifierKeys.NONE);

            input.bind(GameKeys.CAM_FORWARD, Keys.W, ModifierKeys.NONE);
            input.bind(GameKeys.CAM_BACK, Keys.S, ModifierKeys.NONE);
            input.bind(GameKeys.CAM_LEFT, Keys.A, ModifierKeys.NONE);
            input.bind(GameKeys.CAM_RIGHT, Keys.D, ModifierKeys.NONE);
            input.bind(GameKeys.CAM_ASCEND, Keys.PageUp, ModifierKeys.NONE);
            input.bind(GameKeys.CAM_DESCEND, Keys.PageDown, ModifierKeys.NONE);
            input.bind(GameKeys.CAM_ZOOM_IN, Keys.I, ModifierKeys.NONE);
            input.bind(GameKeys.CAM_ZOOM_OUT, Keys.O, ModifierKeys.NONE);
            input.bind(GameKeys.CAM_ROTATE_UP, Keys.Up, ModifierKeys.NONE);
            input.bind(GameKeys.CAM_ROTATE_DOWN, Keys.Down, ModifierKeys.NONE);
            input.bind(GameKeys.CAM_ROTATE_LEFT, Keys.Left, ModifierKeys.NONE);
            input.bind(GameKeys.CAM_ROTATE_RIGHT, Keys.Right, ModifierKeys.NONE);

            MenuState menu = new MenuState(gameManager, this, graphics.PreferredBackBufferWidth, graphics.PreferredBackBufferHeight);
            //adding this in here to test
            NetLevelState level = new LevelState(gameManager, this, "level_0", true);

            gameManager.pushState(level);
            gameManager.pushState(menu);
            gameManager.pushState(new SignInState(gameManager, this, true));

            base.Initialize();
        }

        /// <summary>
        /// LoadContent will be called once per game and is the place to load
        /// all of your content.
        /// </summary>
        protected override void LoadContent()
        {
            // Create a new SpriteBatch, which can be used to draw textures.
            spriteBatch = new SpriteBatch(GraphicsDevice);

            // TODO: use this.Content to load your game content here
        }

        /// <summary>
        /// UnloadContent will be called once per game and is the place to unload
        /// all content.
        /// </summary>
        protected override void UnloadContent()
        {
            // TODO: Unload any non ContentManager content here
        }

        /// <summary>
        /// Allows the game to run logic such as updating the world,
        /// checking for collisions, gathering input, and playing audio.
        /// </summary>
        /// <param name="gameTime">Provides a snapshot of timing values.</param>
        protected override void Update(GameTime gameTime)
        {
            DeviceInput.getInput().poll();

            gameManager.update(gameTime);

            networkManager.update();

            base.Update(gameTime);
        }

        /// <summary>
        /// This is called when the game should draw itself.
        /// </summary>
        /// <param name="gameTime">Provides a snapshot of timing values.</param>
        protected override void Draw(GameTime gameTime)
        {
            graphics.GraphicsDevice.Clear(Color.Black);
            gameManager.render(graphics.GraphicsDevice, spriteBatch);

            // TODO: Add your drawing code here
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

        public NetworkManager getNetworkManager()
        {
            return networkManager;
        }
    }
}
