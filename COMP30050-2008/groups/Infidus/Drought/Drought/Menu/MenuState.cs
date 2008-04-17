using System;
using System.Collections.Generic;
using System.Text;
using Microsoft.Xna.Framework.Content;
using Microsoft.Xna.Framework.Graphics;
using Microsoft.Xna.Framework;
using Drought.State;
using Drought.Input;
using Drought.GameStates;
using Drought.World;
using Drought.Network;

namespace Drought.Menu
{
    /** All the possible functions that can be performed from the menu. */
    enum MenuFunctions { NONE, LOCALLIST, LOCALLIST_BACK, LOCAL, HOSTLIST, HOSTLIST_BACK, HOST,
                            JOINLIST, JOINLIST_BACK, JOIN, QUIT, QUIT_YES, QUIT_NO };

    class MenuState : GameState, IMenuListener
    {
        private DeviceInput input; 

        private Menu mainMenu, localMenu, hostMenu, joinMenu, quitMenu;

        private Menu currMenu;

        private SpriteFont defaultFont;

        private bool canNext, canPrev, canPress;

        private int screenWidth;

        private int screenHeight;

        private NetworkManager networkManager;

        public MenuState(IStateManager manager, DroughtGame game, int width, int height)
            : base(manager, game)
        {
            screenWidth = width;
            screenHeight = height;
            loadContent();
            initialise();
            networkManager = game.getNetworkManager();
        }

        private void initialise()
        {
            input = DeviceInput.getInput();

            canNext = true;
            canPrev = true;
            canPress = true;

            float scale = 0.35f * (screenHeight / 600.0f);
            float mainX = 25.0f * (screenWidth / 800.0f);
            float mainY = 300.0f * (screenHeight / 600.0f);
            float mainSpacing = 70.0f * (screenHeight / 600.0f);
            //Console.WriteLine("scale = " + scale + ", x = " + mainX + ", y = " + mainY + ", yspacing = " + mainSpacing);
            
            mainMenu = new Menu(this);
            mainMenu.activate();

            MenuItem localGame = new MenuItem(MenuFunctions.LOCALLIST, "Local Game", defaultFont);
            localGame.setScale(scale);
            localGame.position = new Vector2(mainX, mainY);
            mainMenu.addSelectableItem(localGame);
            mainY += mainSpacing;

            MenuItem hostGame = new MenuItem(MenuFunctions.HOSTLIST, "Host Game", defaultFont);
            hostGame.setScale(scale);
            hostGame.position = new Vector2(mainX, mainY);
            mainMenu.addSelectableItem(hostGame);
            mainY += mainSpacing;

            MenuItem joinGame = new MenuItem(MenuFunctions.JOINLIST, "Join Game", defaultFont);
            joinGame.setScale(scale);
            joinGame.position = new Vector2(mainX, mainY);
            mainMenu.addSelectableItem(joinGame);
            mainY += mainSpacing;

            MenuItem quit = new MenuItem(MenuFunctions.QUIT, "Quit", defaultFont);
            quit.setScale(scale);
            quit.position = new Vector2(mainX, mainY);
            mainMenu.addSelectableItem(quit);
            mainY += mainSpacing;

            localMenu = new Menu(this);
            
            hostMenu = new Menu(this);

            joinMenu = new Menu(this);

            float quitX = 500.0f * (screenWidth / 800.0f);
            float quitY = 300.0f * (screenHeight / 600.0f);
            quitMenu = new Menu(this);

            MenuItem quitInfo = new MenuItem(MenuFunctions.NONE, "Are you sure?", defaultFont);
            quitInfo.setScale(scale);
            quitInfo.position = new Vector2(quitX, quitY);
            quitInfo.setDefaultColor(Color.Blue);
            quitMenu.addNonSelectableItem(quitInfo);
            quitY += mainSpacing;

            MenuItem quitYes = new MenuItem(MenuFunctions.QUIT_YES, "Yes", defaultFont);
            quitYes.setScale(scale);
            quitYes.position = new Vector2(quitX, quitY);
            quitMenu.addSelectableItem(quitYes);
            quitY += mainSpacing;

            MenuItem quitNo = new MenuItem(MenuFunctions.QUIT_NO, "No", defaultFont);
            quitNo.setScale(scale);
            quitNo.position = new Vector2(quitX, quitY);
            quitMenu.addSelectableItem(quitNo);
            
            currMenu = mainMenu;
        }

        public override void loadContent()
        {
            defaultFont = getContentManager().Load<SpriteFont>("Fonts\\TestFont");
        }

        public override void background() { }

        public override void foreground() { }

        public override void update(GameTime gameTime)
        {
            if (input.isKeyPressed(GameKeys.MENU_NEXT))
            {
                if(canNext)
                {
                    currMenu.nextItem();
                    canNext = false;
                }
            }
            else
                canNext = true;

            if (input.isKeyPressed(GameKeys.MENU_PREV))
            {
                if (canPrev)
                {
                    currMenu.prevItem();
                    canPrev = false;
                }
            }
            else
                canPrev = true;

            if (input.isKeyPressed(GameKeys.MENU_PRESS))
            {
                if (canPress)
                {
                    currMenu.pressItem();
                    canPress = false;
                }
            }
            else
                canPress = true;
        }

        public override void render(GraphicsDevice graphics, SpriteBatch spriteBatch)
        {
            spriteBatch.Begin();
            mainMenu.render(spriteBatch);
            localMenu.render(spriteBatch);
            hostMenu.render(spriteBatch);
            joinMenu.render(spriteBatch);
            quitMenu.render(spriteBatch);
            spriteBatch.End();
        }

        public void menuItemPressed(MenuItem item)
        {
            switch (item.getFunction())
            {
                case MenuFunctions.LOCALLIST: makeLocalList(); currMenu = localMenu; localMenu.activate(); break;
                case MenuFunctions.LOCALLIST_BACK: currMenu = mainMenu; localMenu.deactivate(); break;
                case MenuFunctions.LOCAL: 
                    getStateManager().pushState(new LevelState(getStateManager(), getGame(), ((LevelMenuItem)item).getLevel())); break;

                case MenuFunctions.HOSTLIST: makeHostList(); currMenu = hostMenu; hostMenu.activate(); break;
                case MenuFunctions.HOSTLIST_BACK: currMenu = mainMenu; hostMenu.deactivate(); break;
                case MenuFunctions.HOST: networkManager.host(((LevelMenuItem)item).getLevel());
                    getStateManager().pushState(new NetLevelState(getStateManager(), getGame(), ((LevelMenuItem)item).getLevel(), true));
                    getStateManager().pushState(new HostWaitState(getStateManager(), getGame())); break;
                
                case MenuFunctions.JOINLIST: makeJoinList(); currMenu = joinMenu; joinMenu.activate(); break;
                case MenuFunctions.JOINLIST_BACK: currMenu = mainMenu; joinMenu.deactivate(); break;
                case MenuFunctions.JOIN: networkManager.connectToGame(((JoinLevelMenuItem)item).getGame());
                    getStateManager().pushState(new NetLevelState(getStateManager(), getGame(), ((LevelMenuItem)item).getLevel(), false)); break;
                
                case MenuFunctions.QUIT: currMenu = quitMenu; quitMenu.activate(); break;
                case MenuFunctions.QUIT_YES: getStateManager().popState(); break;
                case MenuFunctions.QUIT_NO: currMenu = mainMenu; quitMenu.deactivate(); break;
            }
        }

        /** Populates the list of playable maps. */
        private void makeLocalList()
        {
            localMenu = new Menu(this);
            float scale = 0.35f * (screenHeight / 600.0f);
            float gameX = 500.0f * (screenWidth / 800.0f);
            float gameY = 100.0f * (screenHeight / 600.0f);
            float spacing = 70.0f * (screenHeight / 600.0f);
            MenuItem header = new MenuItem(MenuFunctions.NONE, "Pick a Level:", defaultFont);
            header.setScale(scale);
            header.position = new Vector2(gameX, gameY);
            header.setDefaultColor(Color.Blue);
            localMenu.addNonSelectableItem(header);
            gameY += spacing;
            foreach (Level levelName in Enum.GetValues(typeof(Level))) {
                MenuItem aLevel = new LevelMenuItem(MenuFunctions.LOCAL, levelName.ToString(), defaultFont, levelName);
                aLevel.setScale(scale);
                aLevel.position = new Vector2(gameX, gameY);
                localMenu.addSelectableItem(aLevel);
                gameY += spacing;
            }
            MenuItem back = new MenuItem(MenuFunctions.LOCALLIST_BACK, "Back", defaultFont);
            back.setScale(scale);
            back.position = new Vector2(gameX, gameY);
            back.setDefaultColor(Color.Gray);
            localMenu.addSelectableItem(back);
        }

        /** Populates the list of playable maps. */
        private void makeHostList()
        {
            hostMenu = new Menu(this);
            float scale = 0.35f * (screenHeight / 600.0f);
            float gameX = 500.0f * (screenWidth / 800.0f);
            float gameY = 100.0f * (screenHeight / 600.0f);
            float spacing = 70.0f * (screenHeight / 600.0f);
            MenuItem header = new MenuItem(MenuFunctions.NONE, "Pick a Level:", defaultFont);
            header.setScale(scale);
            header.position = new Vector2(gameX, gameY);
            header.setDefaultColor(Color.Blue);
            hostMenu.addNonSelectableItem(header);
            gameY += spacing;
            foreach (Level bleh in Enum.GetValues(typeof(Level))) {
                MenuItem aLevel = new LevelMenuItem(MenuFunctions.HOST, bleh.ToString(), defaultFont, bleh);
                aLevel.setScale(scale);
                aLevel.position = new Vector2(gameX, gameY);
                hostMenu.addSelectableItem(aLevel);
                gameY += spacing;
            }
            MenuItem back = new MenuItem(MenuFunctions.HOSTLIST_BACK, "Back", defaultFont);
            back.setScale(scale);
            back.position = new Vector2(gameX, gameY);
            back.setDefaultColor(Color.Gray);
            hostMenu.addSelectableItem(back);

        }

        /** Populates the list of joinable games. */
        private void makeJoinList()
        {
            List<RemoteGame> remoteGames = networkManager.getLocalGames();
            joinMenu = new Menu(this);
            float scale = 0.35f * (screenHeight / 600.0f);
            float gameX = 500.0f * (screenWidth / 800.0f);
            float gameY = 100.0f * (screenHeight / 600.0f);
            float spacing = 70.0f * (screenHeight / 600.0f);
            MenuItem gameCount = new MenuItem(MenuFunctions.NONE, "<" + remoteGames.Count + " Games Found>", defaultFont);
            gameCount.setScale(scale);
            gameCount.position = new Vector2(gameX, gameY);
            gameCount.setDefaultColor(Color.Blue);
            joinMenu.addNonSelectableItem(gameCount);
            gameY += spacing;
            foreach (RemoteGame remoteGame in remoteGames) {
                Level theLevel = (Level) remoteGame.getSession().SessionProperties[0];
                MenuItem aGame = new JoinLevelMenuItem(MenuFunctions.JOIN, remoteGame.getDescription(), defaultFont, theLevel, remoteGame);
                aGame.setScale(scale);
                aGame.position = new Vector2(gameX, gameY);
                joinMenu.addSelectableItem(aGame);
                gameY += spacing;
            }
            MenuItem back = new MenuItem(MenuFunctions.JOINLIST_BACK, "Back", defaultFont);
            back.setScale(scale);
            back.position = new Vector2(gameX, gameY);
            joinMenu.addSelectableItem(back);
        }
    }
}
