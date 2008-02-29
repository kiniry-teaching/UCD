using System;
using System.Collections.Generic;
using System.Text;

namespace drought_states
{
    /**
     * <code>IStateManager</code> describes the interface for states to
     * communicate with the class that is responsible for them.
     */
    public interface IStateManager
    {
       /**
        * Pushes a state on top of the states stack. The state's
        * <code>enter()</code> method is called when the state change actually
        * happens. If there is a state below it in the stack, that state's
        * <code>background</code> method is called.
        * 
        * @param state The state to push.
        */
        void pushState(GameState state);
      
       /**
        * Pops the state on top of the stack. The state's <code>exit()</code>
        * method is called. If there is a state below the popped state, it is
        * brought back into the foreground.
        */
        void popState();
    }
}
