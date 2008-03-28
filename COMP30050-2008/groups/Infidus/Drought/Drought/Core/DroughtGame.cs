using System;
using Microsoft.Xna.Framework;
using Microsoft.Xna.Framework.GamerServices;
using Microsoft.Xna.Framework.Graphics;
using Microsoft.Xna.Framework.Input;
using Drought.Menu;
using Drought.Input;
using Drought.GameStates;
using Drought.Network;
using Drought.Sound;

namespace Drought
{
    /**
     * The entry point of a game.
     * Initialises the GameManager and NetworkManager, sets up the initial states and binds game keys.
     */
    public class DroughtGame : Microsoft.Xna.Framework.Game
    {
        GraphicsDeviceManager graphics;
        SpriteBatch spriteBatch;
        GameManager gameManager;
        SoundManager soundManager;
        NetworkManager networkManager;

        /**
         * So we can turn it off for testing, since it takes so damn long to start up.
         * NOTE: Only prevents the Gamer Services component from being initialized; if
         * a game tries to host or join a game, nasty exceptions will ensue.
         */
        public static readonly bool NETWORKED = true;

        public DroughtGame()
        {
            graphics = new GraphicsDeviceManager(this);
            Content.RootDirectory = "Content";
            IsMouseVisible = true;
            if (NETWORKED) {
                Components.Add(new GamerServicesComponent(this));
            }
            gameManager = new GameManager(this);
            soundManager = SoundManager.getInstance();
            networkManager = NetworkManager.getInstance();
        }

        /**
         * Sets the screen size, and creates keybindings.
         */
        protected override void Initialize()
        {
            graphics.PreferredBackBufferWidth = 800;
            graphics.PreferredBackBufferHeight = 600;
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
            
            input.bind(GameKeys.UNIT_SELECT, MouseButtons.LEFT, ModifierKeys.NONE);
            input.bind(GameKeys.UNIT_COMMAND, MouseButtons.RIGHT, ModifierKeys.NONE);
            input.bind(GameKeys.UNIT_SPAWN, MouseButtons.LEFT, ModifierKeys.SHIFT);
            input.bind(GameKeys.UNIT_DELETE, MouseButtons.RIGHT, ModifierKeys.SHIFT);
            input.bind(GameKeys.UNIT_SELECT_ALL, Keys.E, ModifierKeys.NONE);
            
            input.bind(GameKeys.RESET, Keys.R, ModifierKeys.CTRL);
            input.bind(GameKeys.ADD_WATER, Keys.W, ModifierKeys.CTRL);
            input.bind(GameKeys.PAUSE_SUN, Keys.P, ModifierKeys.CTRL);

            MenuState menu = new MenuState(gameManager, this, graphics.PreferredBackBufferWidth, graphics.PreferredBackBufferHeight);

            gameManager.pushState(menu);
            gameManager.pushState(new SignInState(gameManager, this, true));

            base.Initialize();
        }

        protected override void LoadContent()
        {
            spriteBatch = new SpriteBatch(GraphicsDevice);
        }

        protected override void UnloadContent()
        {
            spriteBatch.Dispose();
            spriteBatch = null;
        }

        /**
         * Gets the latest input state and updates the GameManager and NetworkManager.
         */
        protected override void Update(GameTime gameTime)
        {
            //Console.WriteLine("Update Called");

            DeviceInput.getInput().poll();

            gameManager.update(gameTime);

            soundManager.update();
            networkManager.update();

            base.Update(gameTime);
        }

        /**
         * Draws the current game state.
         */
        protected override void Draw(GameTime gameTime)
        {
            //Console.WriteLine("Render Called");

            graphics.GraphicsDevice.Clear(Color.Black);
            
            gameManager.render(graphics.GraphicsDevice, spriteBatch);

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

        public SoundManager getSoundManager()
        {
            return soundManager;
        }

        public static void Main(string[] args) {
            using (DroughtGame game = new DroughtGame()) {
                game.Run();
            }
        }
    }
}
