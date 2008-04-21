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
     * Initialises the GameManager, SoundManager and NetworkManager,
     * sets up the initial states and binds game keys.
     */
    class DroughtGame : Microsoft.Xna.Framework.Game
    {
        private GraphicsDeviceManager graphics;
        private SpriteBatch spriteBatch;
        private GameManager gameManager;
        private SoundManager soundManager;
        private NetworkManager networkManager;

        /**
         * So we can turn it off for testing, since it takes so damn long to start up.
         * NOTE: Only prevents the Gamer Services component from being initialized; if
         * a game tries to host or join a game, nasty exceptions will ensue.
         */
        public static readonly bool NETWORKED = false;

        public DroughtGame()
        {
            graphics = new GraphicsDeviceManager(this);
            Content.RootDirectory = "Content";
            IsMouseVisible = true;
            if (NETWORKED) Components.Add(new GamerServicesComponent(this));
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

            createKeyBindings();

            MenuState menu = new MenuState(gameManager, this, graphics.PreferredBackBufferWidth, graphics.PreferredBackBufferHeight);
            gameManager.pushState(menu);
            if (NETWORKED) gameManager.pushState(new SignInState(gameManager, this, true));

            base.Initialize();
        }
        
        private void createKeyBindings()
        {
            DeviceInput input = DeviceInput.getInput();

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
            input.bind(GameKeys.UNIT_SPAWN_TANKER, MouseButtons.LEFT, ModifierKeys.SHIFT);
            input.bind(GameKeys.UNIT_SPAWN_SCOUT, MouseButtons.LEFT, ModifierKeys.CTRL);
            input.bind(GameKeys.UNIT_SPAWN_GUARD, MouseButtons.LEFT, ModifierKeys.ALT);
            input.bind(GameKeys.UNIT_DELETE, MouseButtons.RIGHT, ModifierKeys.SHIFT);
            input.bind(GameKeys.UNIT_SELECT_ALL, Keys.E, ModifierKeys.NONE);
            
            input.bind(GameKeys.RESET, Keys.R, ModifierKeys.CTRL);
            input.bind(GameKeys.PAUSE_SUN, Keys.P, ModifierKeys.CTRL);
            input.bind(GameKeys.TOGGLE_FULLSCREEN, Keys.F, ModifierKeys.CTRL);
            input.bind(GameKeys.BURN_BABY_BURN, Keys.F, ModifierKeys.NONE);
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
            DeviceInput.getInput().poll();

            checkFullscreen();

            gameManager.update(gameTime);

            soundManager.update();
            networkManager.update();

            base.Update(gameTime);
        }

        private void checkFullscreen()
        {
            if (DeviceInput.getInput().wasKeyJustPressed(GameKeys.TOGGLE_FULLSCREEN))
            {
                if (graphics.IsFullScreen)
                {
                    graphics.PreferredBackBufferWidth = 800;
                    graphics.PreferredBackBufferHeight = 600;
                    graphics.IsFullScreen = false;
                }
                else
                {
                    graphics.PreferredBackBufferWidth = graphics.GraphicsDevice.DisplayMode.Width;
                    graphics.PreferredBackBufferHeight = graphics.GraphicsDevice.DisplayMode.Height;
                    graphics.IsFullScreen = true;
                }
                graphics.ApplyChanges();
            }
        }

        /**
         * Draws the current game state.
         */
        protected override void Draw(GameTime gameTime)
        {
            graphics.GraphicsDevice.Clear(Color.Black);
            
            gameManager.render(gameTime, graphics.GraphicsDevice, spriteBatch);

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
