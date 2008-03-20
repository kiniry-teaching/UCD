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
    class FixedBall : Image
    {
        #region Fields (core, colour, initialRoatation, coreDistance)

        Core core;
        value colour;
        float initialRotation, coreDistance;
        bool dead, locked;
        List<FixedBall> inContact;
        public int numInContact;

        #endregion

        #region Main Methods(FixedBall, Initialise)

        /*
         * Constructo for FixedBall
         * */
        public FixedBall(Core c, value v) 
        {
            core = c;
            colour = v;    
        }

        /*
         * Initialise starting values
         * */
        public override void Initialise(Game g)
        {
            locked = true;
            dead = false;
            inContact = new List<FixedBall>();
            inContact.Add(this);
            numInContact++;
            base.Initialise(g);
            coreDistance = Vector2.Distance(Position, core.Position);
            //rotation = core.Rotation;
            if (((core.Position.X - Position.X) / coreDistance) > Math.PI)
            {
                initialRotation = (float) Math.Sin((core.Position.Y - Position.Y + 0.53*origin.Y ) / coreDistance);
            }
            else
            {
                initialRotation = (float) (Math.PI + Math.Sin((core.Position.Y - Position.Y + 0.53*origin.Y) / coreDistance));
            }
            // initialRotation = (float)(Math.Sin((core.Position.X - Position.X) / coreDistance) + Math.Sin((core.Position.Y - Position.Y) / coreDistance));
        }

        #endregion

        #region Action Methods (GetRotation, Move, Destroy, IsDead, Unlock, SetCollisionBalls, UpdateCollisionBalls)

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
         * Move the FixedBall
         * */
        public void Move(float rotate)
        {
            GetRotation(rotate);
        }

        /*
         * Set the ball to dead
         * */
        public void Destroy()
        {
            dead = true;
        }

        /*
         * Determine if the ball is dead
         * */
        public bool IsDead()
        {
            return dead;
        }

        /*
         * Not currently implemented
         * */
        public void Unlock()
        {
            locked = false;
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

        #endregion

    }
}
