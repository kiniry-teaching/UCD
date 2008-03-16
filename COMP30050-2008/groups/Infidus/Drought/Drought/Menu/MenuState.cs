using System;
using System.Collections.Generic;
using System.Text;

using Microsoft.Xna.Framework.Content;
using Microsoft.Xna.Framework.Graphics;
using Microsoft.Xna.Framework;
using Drought.State;
using Drought.Input;
using Drought.GameStates;
using Drought.Network;

namespace Drought.Menu
{
    /** All the possible functions that can be performed from the menu. */
    enum MenuFunctions { NONE, QUIT, QUIT_YES, QUIT_NO, HOST, GAMELIST, GAMELIST_BACK, JOIN };


    class MenuState : GameState, IMenuListener
    {
        private DeviceInput input; 

        private Menu mainMenu;

        private Menu quitMenu;

        private Menu joinMenu;

        private Menu currMenu;

        private SpriteFont defaultFont;

        private Color defaultColor;

        private bool canNext;

        private bool canPrev;

        private bool canPress;

        private int screenWidth;

        private int screenHeight;


        public MenuState(IStateManager manager, Game game, int width, int height)
            : base(manager, game)
        {
            screenWidth = width;
            screenHeight = height;
            loadContent();
            initialise();
        }

        private void initialise()
        {
            input = DeviceInput.getInput();
            defaultColor = Color.White;

            canNext = true;
            canPrev = true;
            canPress = true;

            float scale = 0.35f * (screenHeight / 600.0f);
            float mainX = 25.0f * (screenWidth / 800.0f);
            float mainY = 300.0f * (screenHeight / 600.0f);
            float mainSpacing = 70.0f * (screenHeight / 600.0f);
            Console.WriteLine("scale = " + scale + ", x = " + mainX + ", y = " + mainY + ", yspacing = " + mainSpacing);
            
            mainMenu = new Menu(this);
            mainMenu.activate();

            MenuItem hostGame = new MenuItem(MenuFunctions.HOST, "Host Game", defaultFont);
            hostGame.setScale(scale);
            hostGame.position = new Vector2(mainX, mainY);
            mainMenu.addSelectableItem(hostGame);
            mainY += mainSpacing;

            MenuItem joinGame = new MenuItem(MenuFunctions.GAMELIST, "Join Game", defaultFont);
            joinGame.setScale(scale);
            joinGame.position = new Vector2(mainX, mainY);
            mainMenu.addSelectableItem(joinGame);
            mainY += mainSpacing;

            MenuItem quit = new MenuItem(MenuFunctions.QUIT, "Quit", defaultFont);
            quit.setScale(scale);
            quit.position = new Vector2(mainX, mainY);
            mainMenu.addSelectableItem(quit);
            mainY += mainSpacing;


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

            joinMenu = new Menu(this); 
            
            currMenu = mainMenu;
        }

        public override void loadContent()
        {
            defaultFont = getContentManager().Load<SpriteFont>("Fonts\\TestFont");
        }

        public override void background()
        {

        }

        public override void foreground()
        {

        }

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
            quitMenu.render(spriteBatch);
            joinMenu.render(spriteBatch);
            spriteBatch.End();
        }

        public void menuItemPressed(MenuItem item)
        {
            switch (item.getFunction())
            {
                case MenuFunctions.QUIT: currMenu = quitMenu; quitMenu.activate(); break;
                case MenuFunctions.QUIT_YES: getStateManager().popState(); break;
                case MenuFunctions.QUIT_NO: currMenu = mainMenu; quitMenu.deactivate(); break;

                case MenuFunctions.HOST: ((Game1)getGame()).getNetworkManager().host(); getStateManager().pushState(new LevelState(getStateManager(), getGame(), "level_0")); break;
                case MenuFunctions.GAMELIST: if (Game1.NETWORKED) { makeGameList(); currMenu = joinMenu; joinMenu.activate(); } break;
                case MenuFunctions.GAMELIST_BACK: currMenu = mainMenu; joinMenu.deactivate(); break;
                case MenuFunctions.JOIN: ((Game1)getGame()).getNetworkManager().connectToGame(((GameMenuItem)item).getGame()); getStateManager().pushState(new LevelState(getStateManager(), getGame(), "level_0")); break;
            }
        }

        /** Populates the list of joinable games. */
        public void makeGameList() {
            List<RemoteGame> remoteGames = ((Game1)getGame()).getNetworkManager().getLocalGames();
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
                MenuItem aGame = new GameMenuItem(MenuFunctions.JOIN, remoteGame.getDescription(), defaultFont, remoteGame);
                aGame.setScale(scale);
                aGame.position = new Vector2(gameX, gameY);
                joinMenu.addSelectableItem(aGame);
                gameY += spacing;
            }
            MenuItem back = new MenuItem(MenuFunctions.GAMELIST_BACK, "Back", defaultFont);
            back.setScale(scale);
            back.position = new Vector2(gameX, gameY);
            joinMenu.addSelectableItem(back);
        }
    }
}
