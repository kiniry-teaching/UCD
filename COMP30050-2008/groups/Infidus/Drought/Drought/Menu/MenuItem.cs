using System;
using System.Collections.Generic;
using System.Text;
using Microsoft.Xna.Framework;
using Microsoft.Xna.Framework.Graphics;

namespace Drought.Menu
{

    class MenuItem
    {
        /** Item's position on screen in pixels. */
        Vector2 pos;

        /** The function that should be performed when the item is pressed. */
        private MenuFunctions function;

        /** True if the item is selected. */
        private bool isSelected;

        /** Text to display for the item. */
        private String text;

        /** Scale of the item's text. */
        private float scale;

        /** Colour to draw the item when it is not selected. */
        private Color defaultColor;

        /** Colour to draw the item when it is selected. */
        private Color selectedColor;

        /** Font to draw the item's text in. */
        private SpriteFont font;


        /**
         * Constructs a new MenuItem.
         * 
         * @param function The function that should be performed by the item.
         * @param text The text to render for the item.
         * @param font The font to use to render the item's text.
         */
        public MenuItem(MenuFunctions function, String text, SpriteFont font)
        {
            initialise(function, text, font, 1.0f, 0, 0);
        }

        /**
         * Initilises the item.
         * 
         * @param function The function that should be performed by the item.
         * @param text The text to render for the item.
         * @param font The font to use to render the item's text.
         * @param scale The scale of the item's text.
         * @param x The x coordinate of the item in pixels.
         * @param y the y coordinate of the item in pixels.
         */
        private void initialise(MenuFunctions function, String text, SpriteFont font, float scale, int x, int y)
        {
            this.function = function;
            this.text = text;
            this.scale = scale;
            this.font = font;
            isSelected = false;
            pos= new Vector2(x, y);
            defaultColor = Color.White;
            selectedColor = Color.Red;
        }

        /**
         * Draws the item to the screen.
         * It is assumed that the Begin() function has already been called
         * on sprite batch and it is ready for drawing in its current state.
         * 
         * @param spriteBatch The spritebatch to use to draw the item.
         */
        public void render(SpriteBatch spriteBatch)
        {
            spriteBatch.DrawString(font, text, position, selected ? selectedColor : defaultColor,
                0.0f, position, scale, SpriteEffects.None, 0.0f);
        }

        /**
         * Gets/sets the item's position.
         */
        public Vector2 position
        {
            get { return pos; }
            set { pos = value; }
        }

        /**
         * Gets/sets whether the item is selected.
         */
        public bool selected
        {
            get { return isSelected; }
            set { isSelected = value; }
        }

        /**
         * Sets the colour to draw the item when it is selected.
         * 
         * @param c The colour to draw.
         */
        public void setSelectedColor(Color c)
        {
            if(c != null)
                selectedColor = c;
        }

        /**
        * Sets the colour to draw the item when it is not selected.
        * 
        * @param c The colour to draw.
        */
        public void setDefaultColor(Color c)
        {
            if(c != null)
                defaultColor = c;
        }

        /**
         * Sets the scale at which to draw the item's text.
         * 1.0f is the default font size.
         * 
         * @param scale The scale to draw the text at.
         */
        public void setScale(float scale)
        {
            this.scale = scale;
        }

        /**
         * Gets the function the item should perform when it is
         * pressed.
         * 
         * @return The function to perform.
         */
        public MenuFunctions getFunction()
        {
            return function;
        }
    }
}
