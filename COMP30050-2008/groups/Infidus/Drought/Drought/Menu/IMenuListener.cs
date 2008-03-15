using System;
using System.Collections.Generic;
using System.Text;

namespace Drought.Menu
{
    interface IMenuListener
    {
        /**
         * The logic to execute when at item has been pressed.
         * 
         * @param item The item that was activated.
         */
        void menuItemPressed(MenuItem item);
    }
}
