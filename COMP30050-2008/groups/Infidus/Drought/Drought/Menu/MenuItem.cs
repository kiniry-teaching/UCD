using System;
using System.Collections.Generic;
using System.Text;
using Microsoft.Xna.Framework;
using Microsoft.Xna.Framework.Graphics;

namespace drought_states.menu
{

    class MenuItem
    {
        Vector2 pos;

        private MenuFunctions function;

        private bool isSelected;

        private String text;

        private String toolTipText;

        private float scale;

        private Color defaultColor;

        private Color selectedColor;

        private SpriteFont font;


        public MenuItem(MenuFunctions function, String text, SpriteFont font)
        {
            initialise(function, text, "", font, 1.0f, 0, 0);
        }

        private void initialise(MenuFunctions function, String text, String toolTip, SpriteFont font, float scale, int x, int y)
        {
            this.function = function;
            this.text = text;
            this.toolTipText = toolTip;
            this.scale = scale;
            this.font = font;
            isSelected = false;
            pos= new Vector2(x, y);
            defaultColor = Color.White;
            selectedColor = Color.Red;
        }

        public void update()
        {

        }

        public void render(SpriteBatch spriteBatch)
        {
            spriteBatch.DrawString(font, text, position, selected ? selectedColor : defaultColor,
                0.0f, position, scale, SpriteEffects.None, 0.0f);
        }

        public Vector2 position
        {
            get { return pos; }
            set { pos = value; }
        }

        public bool selected
        {
            get { return isSelected; }
            set { isSelected = value; }
        }
        
        public String toolTip
        {
            get { return toolTipText; }
            set { toolTipText = value; }
        }

        public void setSelectedColor(Color c)
        {
            if(c != null)
                selectedColor = c;
        }

        public void setDefaultColor(Color c)
        {
            if(c != null)
                defaultColor = c;
        }

        public void setScale(float scale)
        {
            this.scale = scale;
        }

        public MenuFunctions getFunction()
        {
            return function;
        }
    }
}
