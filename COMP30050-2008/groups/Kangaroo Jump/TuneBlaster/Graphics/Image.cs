using System;
using System.Collections.Generic;
using System.Text;
using Microsoft.Xna.Framework;
using Microsoft.Xna.Framework.Graphics;

namespace TuneBlaster_.Graphics
{
    /// <summary>
    /// The base class for everything that appears onscreen
    /// Author Hugh Corrigan, Ahmed Warreth, Dermot Kirby
    /// </summary>
    class Image
    {
        

        #region Properties (Position, Rotation, Size)

        public Vector2 Position
        {
            get { return position; }
            set { position = value; }
        }

        public float Rotation
        {
            get { return rotation; }
            set { rotation = value; }
        }

        public Vector2 Size
        {
            get { return size; }
            set { size = value; }
        }

        public Vector2 Origin
        {
            get { return origin; }
            set { origin = value; }
        }

        #endregion

        #region Field (spritebatch, texture, position, source, colour, rotation, origin, scale, efftects, layer, size, value)

        public enum value { red, green, blue, purple, none }
        public SpriteBatch spriteBatch;
        public Texture2D texture;
        private Vector2 position;
        protected Rectangle source;
        private Color colour;
        protected float rotation;
        protected Vector2 origin;
        private Vector2 scale;
        private SpriteEffects effects;
        private float layer;
        protected Vector2 size;
        public Game game;

        #endregion

        #region Main methods (LoadGraphicsContents, Initialise, Draw, Update)

        /*
         * Load info to Graphics memory
         */
        public void LoadGraphicsContent(SpriteBatch spriteBatch, Texture2D texture)
        {
            this.spriteBatch = spriteBatch;
            this.texture = texture;
        }

        /*
         * Initialse starting values
         */
        public virtual void Initialise(Game g)
        {
            game = g;
            this.colour = Color.White;
            this.rotation = 0f;
            this.scale = Vector2.One;
            this.effects = SpriteEffects.None;
            this.layer = 0.5f;
            this.source = new Rectangle(0, 0, (int)this.size.X, (int)this.size.Y);
            this.origin = new Vector2(source.Width / 2, source.Height / 2);
        }

        /*
         * Initialise starting values with specified position and size
         */
        public virtual void Initialise(Vector2 mySize, Vector2 myPosition, Game g)
        {
            this.size = mySize;
            this.position = myPosition;
            this.Initialise(g);
        }

        /*
         * Draw the image on the spritebatch
         */
        public virtual void Draw(GameTime gameTime)
        {
            this.spriteBatch.Draw(this.texture, this.position, this.source, this.colour, this.rotation, this.origin, this.scale, this.effects, this.layer);    
        }

        /*
         * Update the Image for each frame
         */
        public virtual void Update(GameTime gameTime)
        {
            Move();
        }

        #endregion

        #region Action Methods (Collide, Move)

        /*
         * Check if this is colliding with another Image
         */
        public bool Collide(Image a)
        {
            if (Vector2.Distance(position - origin + size / 2, a.position - a.origin + a.size / 2) < size.X / 2 + a.size.X / 2)
                return true;
            else
                return false;
        }

        /*
         * Move the Image
         */
        public virtual void Move()
        {
        }

        #endregion
    }
}
