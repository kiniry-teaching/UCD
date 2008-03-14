using System;
using System.Collections.Generic;
using System.Text;

using Microsoft.Xna.Framework.Content;
using Microsoft.Xna.Framework.Graphics;
using Microsoft.Xna.Framework;
using Drought.State;
using Drought.Input;
using Drought.GameStates;

namespace Drought.Menu
{
    enum MenuFunctions { NONE, QUIT, QUIT_YES, QUIT_NO, HOST, JOIN, OPTIONS };


    class MenuState : GameState, IMenuListener
    {
        private Input.Input input; 

        private Menu mainMenu;

        private Menu quitMenu;

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
            initialise();
        }

        private void initialise()
        {
            input = Input.Input.getInput();
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

            MenuItem joinGame = new MenuItem(MenuFunctions.JOIN, "Join Game", defaultFont);
            joinGame.setScale(scale);
            joinGame.position = new Vector2(mainX, mainY);
            mainMenu.addSelectableItem(joinGame);
            mainY += mainSpacing;

            MenuItem quit = new MenuItem(MenuFunctions.QUIT, "Quit", defaultFont);
            quit.setScale(scale);
            quit.position = new Vector2(mainX, mainY);
            mainMenu.addSelectableItem(quit);
            mainY += mainSpacing;


            float quitX = 500.0f * (screenWidth / 800.0f); ;
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
            mainMenu.render(graphics, spriteBatch);
            quitMenu.render(graphics, spriteBatch);
        }

        public void menuItemPressed(MenuItem item)
        {
            switch (item.getFunction())
            {
                case MenuFunctions.QUIT: currMenu = quitMenu; quitMenu.activate(); ; break;
                case MenuFunctions.QUIT_YES: getStateManager().popState(); break;
                case MenuFunctions.QUIT_NO: currMenu = mainMenu; quitMenu.deactivate(); break;

                case MenuFunctions.HOST: getStateManager().pushState(new LevelState(getStateManager(), getGame(), "level_0")); break;
            }
        }
    }
}
