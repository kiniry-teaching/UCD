using System;
using System.Collections.Generic;
using System.Text;
using Microsoft.Xna.Framework.Graphics;
using Microsoft.Xna.Framework;

namespace TuneBlaster_.Graphics
{
    /// <summary>
    /// The class for the balls that have become stationary due to a colission
    /// Author Hugh Corrigan
    /// </summary>
    class FixedBall : MovingBall
    {
        #region Fields (core, colour, initialRoatation, coreDistance)

        float initialRotation, coreDistance;
        bool dead, locked, onCore;
        List<FixedBall> inContact;
        List<FixedBall> supports;
        public int numInContact;

        #endregion

        #region Main Methods(FixedBall, Initialise)

        /*
         * Constructo for FixedBall
         * */
        public FixedBall(Core c, value v) : base(c,v)
        {
        }

        /*
         * Initialise starting values
         * */
        public override void Initialise(Game g)
        {
            locked = true;
            dead = false;
            onCore = false;
            game = g;
            bw = game.Content.Load<Texture2D>(@"Resources\Textures\blackwhite");
            inContact = new List<FixedBall>();
            supports = new List<FixedBall>();
            inContact.Add(this);
            numInContact++;
            base.Initialise(g);
            Console.WriteLine(Math.Acos(Vector2.Distance(new Vector2(core.Position.X+ core.Size.X/2, core.Position.Y), new Vector2(Position.X, core.Position.Y))/Vector2.Distance(Position, new Vector2(core.Position.X+ core.Size.X/2, core.Position.Y))));
        }


        #endregion

        #region Action Methods (GetRotation, Move, Destroy, IsDead, Unlock, SetCollisionBalls, UpdateCollisionBalls)

        /*
         * 
         * */
        public void DoAngles()
        {
            coreDistance = Vector2.Distance(Position, core.Position);
            CalculateInitialRotation();
        }

        /*
         * Get rotation based on change in rotation of the core, and initial starting position
         * */
        public void GetRotation(float rotate)
        {
            rotation += rotate;
            initialRotation += rotate;
            Position = core.Position + new Vector2((float)(coreDistance * Math.Cos(initialRotation)), (float) (coreDistance * Math.Sin(initialRotation)));
        }

        /*
         * Calculate the angle between this and the core, so that it's allignment is correct,
         * allowing rotation as one with the core
         * */
        public void CalculateInitialRotation()
        {
            if (Position.Y == core.Position.Y)
            {
                if (Position.X > core.Position.X)
                {
                    initialRotation = 0;
                }

                else
                {
                    initialRotation = (float)Math.PI;
                }
            }

            if (Position.Y <= core.Position.Y)
            {
                //Calculate angle within circle
                double tempAngle = (Math.PI + Math.Acos(Vector2.Distance(new Vector2(core.Position.X + coreDistance, core.Position.Y), new Vector2(Position.X, core.Position.Y)) / Vector2.Distance(Position, new Vector2(core.Position.X + coreDistance, core.Position.Y))));
                //turn to degrees
                tempAngle = tempAngle * 180 / Math.PI;
                //calculate as percentge of full angle
                tempAngle /= 90;
                initialRotation = (float)(Math.PI + tempAngle * Math.PI);
                //initialRotation = 0.2f;
            }

            else
            {
                //Calculate angle within circle
                double tempAngle = (Math.PI + Math.Acos(Vector2.Distance(new Vector2(core.Position.X + coreDistance, core.Position.Y), new Vector2(Position.X, core.Position.Y)) / Vector2.Distance(Position, new Vector2(core.Position.X + coreDistance, core.Position.Y))));
                //turn to degrees
                tempAngle = tempAngle * 180 / Math.PI;
                //calculate as percentge of full angle
                tempAngle /= 90;
                initialRotation = (float)(Math.PI - tempAngle * Math.PI);
                //initialRotation = 0.2f;
            }
        }
        

        /*
         * Move the FixedBall
         * */
        public void Move(float rotate)
        {
            if (colourTexture == null)
            {
                colourTexture = texture;
            }
            SwitchBlack();
            GetRotation(rotate);
        }

        /*
         * Determine if the ball is dead
         * */
        public bool IsDead()
        {
            return dead;
        }

        /*
         * Set the ball to dead
         * */
        public void Destroy()
        {
            dead = true;
        }

        /*
         * Not currently implemented
         * */
        public void Unlock()
        {
            locked = false;
        }

        /*
         * Add a support
         * */
        public void AddSupport(FixedBall f)
        {
            supports.Add(f);
        }

        /*
         * Add a support
         * */
        public bool Unsupported()
        {
            if (supports.Count == 0)
            {
                return true;
            }

            return false;
            
        }

        /*
         * Set the ball to be supported by the core
         * */
        public void SetAgainstCore()
        {
            onCore = true;
        }

        /*
         * Is ball against core
         * */
        public bool IsAgainstCore()
        {
            return onCore;
        }

        /*
         * Set the ball to be supported by the core
         * */
        public void CheckSupports()
        {
            for (int i = 0; i < supports.Count; i++)
            {
                if (supports[i].IsDead())
                {
                    supports.Remove(supports[i]);
                }
            }
        }

        /*
         * Collect the list of balls touching this ball
         * */
        public void SetCollisionBall(FixedBall f)
        {
            // if touching a ball of the same colour
            if (f.colour == colour)
            {
                bool isThere;
                //traverse the list of balls the contacted ball touches
                for (int i = 0; i < f.numInContact; i++)
                {
                    isThere = false;
                    //traverse the list of balls this contacts
                    for (int j = 0; j < this.numInContact; j++)
                    {
                        if (f.inContact[i] == this.inContact[j])
                        {
                            isThere = true;
                        }
                    }
                    //actions if this ball has not "observed" that it is touching the ball in the contacting balls group
                    if (isThere == false)
                    {
                        inContact.Add(f.inContact[i]);
                        numInContact++;
                        f.inContact[i].inContact.Add(this);
                        f.inContact[i].numInContact++;
                    }
                }
            }
        }

        /*
         * Update all balls in contact with this to make sure they are correct
         * */
        public void UpdateContactBalls()
        {
            // traverse the list of balls in contact
            for (int i = 0; i < numInContact; i++)
            {                
                if (this.numInContact != inContact[i].numInContact) {
                    // if the ball is not up do date, traverse the list of balls touching this
                    for (int j = 0; j < numInContact; j++)
                    {
                        bool isThere = false;
                        // see if each ball in this is in the out of date ball
                        for (int k = 0; k < inContact[i].numInContact; k++) 
                        {                            
                            if (inContact[j] == inContact[i].inContact[k])
                            {
                                isThere = true;
                            }                                                   
                        }
                        //if a ball is not there, add it
                        if (isThere == false)
                        {
                            inContact[i].inContact.Add(inContact[j]);
                            inContact[i].numInContact++;
                        }
                    }
                }
            }
        }

        /*
         * 
         * */
        public void CorrectPostion(FixedBall f)
        {
            if (Vector2.Distance(f.Position, Position) < size.X)
            {
                Vector2 d = f.Position - Position;
                d.Normalize();
                d = d * size.X;
                Position = f.Position - d;
            }
        }
        #endregion

    }

}
