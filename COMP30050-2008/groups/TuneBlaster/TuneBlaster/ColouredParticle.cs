

using System;
using System.Collections.Generic;
using System.Text;
using Microsoft.Xna.Framework;
using Microsoft.Xna.Framework.Graphics;
namespace TuneBlaster_
{


    // Author Ahmed Warreth

    

    /// <summary>
    /// specialization of ParticleSystem which the particles effects on screen
    /// </summary>
    public class ColouredParticle : ParticleSystem
    {

        int Colour;
        public ColouredParticle(Engine game, int howManyEffects, int Colour)
            : base(game, howManyEffects)
        {

            this.Colour = Colour;

        }

        /// <summary>
        /// give this the particle system its behavior and
        /// properties.
        /// </summary>
        protected override void InitializeConstants()
        {

            //the textures are loaded here, and given a value from 1-10

            switch (Colour)
            {
                case 1:
                    textureFilename = "redparticle";
                    break;

                case 2:

                    textureFilename = "blueparticle";
                    break;

                case 3:

                    textureFilename = "purpleparticle";
                    break;

                case 4:

                    textureFilename = "greenparticle";
                    break;

                case 5:
                    textureFilename = "explosion";
                    break;


                case 6:
                    textureFilename = "smoke";
                    break;

                case 7:
                    textureFilename = "Rnote";
                    break;

                case 8:
                    textureFilename = "Bnote";
                    break;

                case 9:
                    textureFilename = "Gnote";
                    break;

                case 10:
                    textureFilename = "Pnote";
                    break;


            }





            //particle properties


            minInitialSpeed = 40;
            maxInitialSpeed = 500;

            minAcceleration = 0;
            maxAcceleration = 0;

            
            minLifetime = .5f;
            maxLifetime = 1.0f;

            minScale = .3f;
            maxScale = 1.0f;

            minNumParticles = 20;
            maxNumParticles = 25;

            minRotationSpeed = -MathHelper.PiOver4;
            maxRotationSpeed = MathHelper.PiOver4;


            spriteBlendMode = SpriteBlendMode.Additive;

            DrawOrder = AdditiveDrawOrder;








        }

        //exception handler,

        private void LoadGraphicsContent(SpriteBatch SpriteBatch, object texture)
        {
            throw new Exception("The method or operation is not implemented.");
        }





        protected override void InitializeParticle(Particle p, Vector2 where)
        {
            base.InitializeParticle(p, where);

            // Explosions move outwards, then slow down and stop because of air resistance. he i change the
            // acceleration so that when the particle is at max lifetime, the velocity
            // will be zero.

            // velocity at time t = initial velocity + acceleration * t)
            // for a0, using t = p.Lifetime and vt = 0.
            p.Acceleration = -p.Velocity / p.Lifetime;
        }
    }
}


























