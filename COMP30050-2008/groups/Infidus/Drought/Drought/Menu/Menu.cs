using System;
using System.Collections.Generic;
using System.Text;
using Microsoft.Xna.Framework.Graphics;
using Microsoft.Xna.Framework;

namespace Drought.Menu
{
    class Menu
    {
        private static int NO_ITEM = -2;

        private List<MenuItem> selectableItems;

        private List<MenuItem> nonSelectableItems;

        private int selectedIndex;

        private IMenuListener listener;

        private bool isActive;

        
        public Menu(IMenuListener listener)
        {
            selectableItems = new List<MenuItem>();
            nonSelectableItems = new List<MenuItem>();
            this.listener = listener;
            selectedIndex = NO_ITEM;
            isActive = false;
        }

        public void activate()
        {
            isActive = true;
        }

        public void deactivate()
        {
            isActive = false;
        }

        public void update()
        {

        }

        public void render(GraphicsDevice graphics, SpriteBatch spriteBatch)
        {
            if (!isActive)
                return;

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
