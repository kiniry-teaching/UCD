using System;
using System.Collections.Generic;
using System.Text;
using Microsoft.Xna.Framework.Input;

namespace Drought.Input
{
    /** The game's available commands */
    public enum GameKeys : int { MENU_NEXT, MENU_PREV, MENU_PRESS, UP, DOWN, LEFT, RIGHT, QUIT, CHANGE_STATE,
                                CAM_FORWARD, CAM_BACK, CAM_LEFT, CAM_RIGHT, CAM_ASCEND, CAM_DESCEND, CAM_ZOOM_IN, CAM_ZOOM_OUT,
                                CAM_ROTATE_UP, CAM_ROTATE_DOWN, CAM_ROTATE_LEFT, CAM_ROTATE_RIGHT};

    /** Keys that can be used as modifier keys */
    public enum ModifierKeys : int { NONE, CTRL, ALT, SHIFT };

    /** 
     * Available mouse buttons for binding. Need to provide our own enum as
     * XNA's mouse handler is different than their keyboard's.
     */
    public enum MouseButtons : int { NONE, LEFT, RIGHT, MIDDLE };

    /**
     * The <code>DeviceInput</code> class allows the binding of <code>GameKeys</code>
     * to arbitrary keyboard and mouse buttons. 
     * 
     * Game Key: a representation of a command the user can give to the game. 
     * Device key: a physical button on an input device (keyboard)
     * 
     * Shift, Control and Alt are modifier keys and can be used in creating an 
     * alternate binding for a device key. The <code>Input</code> allows  for 
     * creating key bindings, checking whether a key is pressed and retrieving
     * the mouse position. Since all input comes from the same sources (keyboard,
     * mouse etc.) it makes sense for this class to be a singleton.
     * 
     * Internally, mappings from game keys to devices and from game keys to device keys
     * are stored. When storing the mapping from game keys to device keys an array of 
     * size (number of game keys * number of modifier keys + 1) is used. This is so each 
     * game key can have one mapping for each possible modifier. If the one modifier was
     * used (CTRL) then the first half of the mappings data structure stores the mapping 
     * for when there is no modifier pressed and the second half stores the mappings for
     * when CTRL is pressed.
     * 
     * @author Infidus
     */
    public class DeviceInput
    {
        /** Differet devices that keys can be bound to */
        private enum Devices : int { KEYBOARD, MOUSE, NONE };

        /** 
         * The number of game keys.
         * (same as the number of elements in the GameKeys enumeration)
         */
        private int gameKeyCount;

        /** Stores a mapping from game keys to the devices they are bound to */
        private Devices[] deviceBindings;

        /** Stores a mapping from games keys to the keyboard key they are bound to */
        private Keys[] keyboardBindings;

        /** Stores a mapping from games keys to the mouse button they are bound to */
        private MouseButtons[] mouseBindings;

        /** The current state of the keyboard's buttons */
        private KeyboardState keyboard;
        
        /** The current state of the mouse's buttons */
        private MouseState mouse;

        /** Single instance of the input class */
        private static DeviceInput instance = new DeviceInput();
   
        /**
         * Constructs a new Input class with all the keys bound to
         * no device.
         */
        private DeviceInput()
        {
            gameKeyCount = Enum.GetValues(typeof(GameKeys)).Length;
            int modifierKeyCount = Enum.GetValues(typeof(ModifierKeys)).Length;
            deviceBindings = new Devices[gameKeyCount];
            keyboardBindings = new Keys[gameKeyCount * modifierKeyCount];
            mouseBindings = new MouseButtons[gameKeyCount * modifierKeyCount];

            //set all keys to be binded to nothing initially.
            clearBindings();
        }

        /**
         * Gets the single instance of the input class.
         * 
         * @return Input.
         */
        public static DeviceInput getInput()
        {
            return instance;
        }

        /**
         * Polls the input devices and stores their new states.
         * <c>poll()</c> <b>must</b> be called once each game
         * update in order to have the most up to date device states.
         */
        public void poll()
        {
            keyboard = Keyboard.GetState();
            mouse = Mouse.GetState();
        }

        /**
         * Binds a game key to a specified keyboard key.
         * Keys in an enumeration of keyboard keys and is
         * part of the XNA framework.
         * 
         * @param gameKey The game key to bind.
         * @param key The keyboard key to bind.
         */
        public void bind(GameKeys gameKey, Keys key, ModifierKeys modifier)
        {
            deviceBindings[(int)gameKey] = Devices.KEYBOARD;
            keyboardBindings[(int)gameKey + ((int)modifier * gameKeyCount)] = key;
        }

        /**
         * Binds a game key to a specified mouse button.
         * <code>MouseButtons</code> is an enumeration of
         * the mouse buttons that it is possible to bind to
         * and is part of the <code>GameInput</code> namespace.
         * 
         * @param gameKey The game key to bind.
         * @param button The mouse button to bind.
         */
        public void bind(GameKeys gameKey, MouseButtons button, ModifierKeys modifier)
        {
            deviceBindings[(int)gameKey] = Devices.MOUSE;
            mouseBindings[(int)gameKey + ((int)modifier * gameKeyCount)] = button;
        }

        /**
         * Clears all bindings related to a specific game key.
         * 
         * @param gameKey The game key to clear bindings for.
         */
        public void clearBinding(GameKeys gameKey)
        {
            deviceBindings[(int)gameKey] = Devices.NONE;
            
            mouseBindings[(int)gameKey] = MouseButtons.NONE;
            mouseBindings[(int)gameKey + (gameKeyCount * (int)ModifierKeys.CTRL)] = MouseButtons.NONE;
            mouseBindings[(int)gameKey + (gameKeyCount * (int)ModifierKeys.SHIFT)] = MouseButtons.NONE;
            mouseBindings[(int)gameKey + (gameKeyCount * (int)ModifierKeys.ALT)] = MouseButtons.NONE;

            keyboardBindings[(int)gameKey] = Keys.None;
            keyboardBindings[(int)gameKey + (gameKeyCount * (int)ModifierKeys.CTRL)] = Keys.None;
            keyboardBindings[(int)gameKey + (gameKeyCount * (int)ModifierKeys.SHIFT)] = Keys.None;
            keyboardBindings[(int)gameKey + (gameKeyCount * (int)ModifierKeys.ALT)] = Keys.None;
        }

        /**
         * Clears all the key bindings.
         */
        public void clearBindings()
        {
            for (int i = 0; i < deviceBindings.Length; i++)
                deviceBindings[i] = Devices.NONE;

            for (int i = 0; i < keyboardBindings.Length; i++)
                keyboardBindings[i] = Keys.None;

            for (int i = 0; i < mouseBindings.Length; i++)
                mouseBindings[i] = MouseButtons.NONE;
        }

        /**
         * Checks whether a game key is pressed.
         * 
         * @param gameKey The key to check.
         * @return True if gameKey is pressed.
         */
        public bool isKeyPressed(GameKeys gameKey)
        {
            /*
             * To find out if a key is pressed:
             * 1. A mapping must be queried to determine which device the key is bound to.
             * 2. Modifiers must be checked so the appropiate device key is looked up.
             * 3. Look up device key according to modifiers and game key in a bindings mapping
             *    specific to the device.
             * 4. Check the state of the device key.
             */
            switch (deviceBindings[(int)gameKey])
            {
                case Devices.KEYBOARD:
                    if (keyboard.IsKeyDown(Keys.LeftControl))
                        return keyboard.IsKeyDown(keyboardBindings[(int)gameKey + ((int)ModifierKeys.CTRL * gameKeyCount)]);
                    else if(keyboard.IsKeyDown(Keys.LeftAlt))
                        return keyboard.IsKeyDown(keyboardBindings[(int)gameKey + ((int)ModifierKeys.ALT * gameKeyCount)]);
                    else if(keyboard.IsKeyDown(Keys.LeftShift))
                        return keyboard.IsKeyDown(keyboardBindings[(int)gameKey + ((int)ModifierKeys.SHIFT * gameKeyCount)]);
                    else
                        return keyboard.IsKeyDown(keyboardBindings[(int)gameKey]);
                case Devices.MOUSE:
                    if (keyboard.IsKeyDown(Keys.LeftControl))
                        return isMouseButtonPressed(mouseBindings[(int)gameKey + ((int)ModifierKeys.CTRL * gameKeyCount)]);
                    else if (keyboard.IsKeyDown(Keys.LeftAlt))
                        return isMouseButtonPressed(mouseBindings[(int)gameKey + ((int)ModifierKeys.ALT * gameKeyCount)]);
                    else if (keyboard.IsKeyDown(Keys.LeftShift))
                        return isMouseButtonPressed(mouseBindings[(int)gameKey + ((int)ModifierKeys.SHIFT * gameKeyCount)]);
                    else
                        return isMouseButtonPressed(mouseBindings[(int)gameKey]);
                case Devices.NONE:
                    Console.WriteLine("request for key \"" + gameKey + "\" state but it's not bound!");
                    return false;
                default:
                    return false;
            }
        }

        /**
         * Checks is a button on the mouse is pressed.
         * 
         * @param button The button to check.
         * @return True if the button is pressed.
         */
        private bool isMouseButtonPressed(MouseButtons button)
        {
            switch (button)
            {
                case MouseButtons.LEFT:
                    return mouse.LeftButton == ButtonState.Pressed ? true : false;
                case MouseButtons.RIGHT:
                    return mouse.RightButton == ButtonState.Pressed ? true : false;
                case MouseButtons.MIDDLE:
                    return mouse.MiddleButton == ButtonState.Pressed ? true : false;
                default:
                    return false;
            }
        }

        /**
         * Gets the horizontal position of the mouse cursor in relation to 
         * the upper-left corner of the game window.
         * 
         * @return Mouse's x coordinate.
         */
        public int getMouseX()
        {
            return mouse.X;
        }

        /**
        * Gets the vertical position of the mouse cursor in relation to 
        * the upper-left corner of the game window.
        * 
        * @return Mouse's y coordinate.
        */
        public int getMouseY()
        {
            return mouse.Y;
        }
    }
}
