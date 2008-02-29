using System;
using System.Collections.Generic;
using System.Text;

using Microsoft.Xna.Framework.Content;
using Microsoft.Xna.Framework.Graphics;
using Microsoft.Xna.Framework;

namespace drought_states.menu
{
    enum MenuFunctions { QUIT, HOST, JOIN, OPTIONS };


    class MenuState : GameState, IMenuListener
    {
        private Input input; 

        private Menu mainMenu;

        private Menu currMenu;

        private SpriteFont defaultFont;

        private Color defaultColor;

        private bool canNext;

        private bool canPrev;

        private bool canPress;


        public MenuState(IStateManager manager, ContentManager content)
            : base(manager, content)
        {
            initialise();
        }

        private void initialise()
        {
            input = Input.getInput();
            defaultColor = Color.White;

            canNext = true;
            canPrev = true;
            canPress = true;

            float scale = 0.25f;
            int mainX = 0;
            int mainY = 0;
            int mainSpacing = 50;
            mainMenu = new Menu(this);

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

        public override void render(GraphicsDeviceManager graphics, SpriteBatch spriteBatch)
        {
            currMenu.render(graphics, spriteBatch);
        }

        public void menuItemPressed(MenuItem item)
        {
            switch (item.getFunction())
            {
                case MenuFunctions.QUIT: getStateManager().popState() ; break;
            }
        }
    }
}
