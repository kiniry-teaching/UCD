using System;
using System.Collections.Generic;
using System.Text;
using Microsoft.Xna.Framework.Graphics;
using Microsoft.Xna.Framework;

namespace drought_states.menu
{
    class Menu
    {
        private static int NO_ITEM = -2;

        private List<MenuItem> selectableItems;

        private List<MenuItem> nonSelectableItems;

        private int selectedIndex;

        private IMenuListener listener;

        
        public Menu(IMenuListener listener)
        {
            selectableItems = new List<MenuItem>();
            nonSelectableItems = new List<MenuItem>();
            this.listener = listener;
            selectedIndex = NO_ITEM;
        }

        public void activate()
        {

        }

        public void deactivate()
        {

        }

        public void update()
        {

        }

        public void render(GraphicsDeviceManager graphics, SpriteBatch spriteBatch)
        {
            for (int i = 0; i < selectableItems.Count; i++)
                selectableItems[i].render(spriteBatch);

            for (int i = 0; i < nonSelectableItems.Count; i++)
                nonSelectableItems[i].render(spriteBatch);
        }

        public void addNonSelectableItem(MenuItem item)
        {
            nonSelectableItems.Add(item);
        }

        public void addSelectableItem(MenuItem item)
        {
            selectableItems.Add(item);

            if (selectedIndex == NO_ITEM)
            {
                selectedIndex = 0;
                selectableItems[0].selected = true;
            }
        }

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

        public void pressItem()
        {
            if (selectedIndex != NO_ITEM)
                listener.menuItemPressed(selectableItems[selectedIndex]);
        }
    }   
}
