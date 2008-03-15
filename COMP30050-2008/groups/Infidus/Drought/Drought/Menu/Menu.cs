using System;
using System.Collections.Generic;
using System.Text;
using Microsoft.Xna.Framework.Graphics;
using Microsoft.Xna.Framework;

namespace Drought.Menu
{
    class Menu
    {
        /** Constant indicating that no item in the menu is selected. */
        private static int NO_ITEM = -2;

        /** List of selectable items this menu contains. */
        private List<MenuItem> selectableItems;

        /** List of non-selectable items this menu contains. */
        private List<MenuItem> nonSelectableItems;

        /** Index of the currently selected item in selectableItems or NO_ITEM. */
        private int selectedIndex;

        /** The listener to notify when a function should be performed. */
        private IMenuListener listener;

        /** True if the menu is currently active. */
        private bool isActive;

        /**
         * Constructs a new Menu.
         * 
         * @param listener The listener to notify when an function should be performed.
         */
        public Menu(IMenuListener listener)
        {
            selectableItems = new List<MenuItem>();
            nonSelectableItems = new List<MenuItem>();
            this.listener = listener;
            selectedIndex = NO_ITEM;
            isActive = false;
        }

        /**
         * Set this menu as being active.
         */
        public void activate()
        {
            isActive = true;
        }

        /**
         * Set this menu as being inactive.
         */
        public void deactivate()
        {
            isActive = false;
        }

        /**
         * Draws the menu to the screen.
         * It is assumed that the Begin() function has already been called
         * on sprite batch and it is ready for drawing in its current state.
         * 
         * @param spriteBatch The spritebatch to use to draw the item.
         */
        public void render(SpriteBatch spriteBatch)
        {
            if (!isActive)
                return;

            for (int i = 0; i < selectableItems.Count; i++)
                selectableItems[i].render(spriteBatch);

            for (int i = 0; i < nonSelectableItems.Count; i++)
                nonSelectableItems[i].render(spriteBatch);
        }

        /**
         * Add an item that is not selectable to this menu.
         * 
         * @param item The item to add.
         */
        public void addNonSelectableItem(MenuItem item)
        {
            nonSelectableItems.Add(item);
        }

        /**
         * Add an item that is selectable to this menu.
         * 
         * @param item The item to add.
         */
        public void addSelectableItem(MenuItem item)
        {
            selectableItems.Add(item);

            if (selectedIndex == NO_ITEM)
            {
                selectedIndex = 0;
                selectableItems[0].selected = true;
            }
        }

        /**
         * Select the next item in the menu's selectable items
         * list, if one such item exists.
         */
        public void nextItem()
        {
            if(selectedIndex != NO_ITEM)
            {
                selectableItems[selectedIndex].selected = false;
                selectedIndex++;

                if (selectedIndex == selectableItems.Count)
                    selectedIndex = 0;

                selectableItems[selectedIndex].selected = true;
            }
        }

        /**
         * Select the previous item in the menu's selectable items
         * list, if one such item exists.
         */
        public void prevItem()
        {
            if (selectedIndex != NO_ITEM)
            {
                selectableItems[selectedIndex].selected = false;
                selectedIndex--;

                if (selectedIndex == -1)
                    selectedIndex = selectableItems.Count - 1;

                selectableItems[selectedIndex].selected = true;
            }
        }

        /**
         * Notifies the listener that the currently selected item has been pressed.
         * If no item is selected then nothing happens.
         */
        public void pressItem()
        {
            if (selectedIndex != NO_ITEM)
                listener.menuItemPressed(selectableItems[selectedIndex]);
        }
    }   
}
