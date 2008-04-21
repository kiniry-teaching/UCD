

using System;
using System.Collections.Generic;
using System.Text;
using Microsoft.Xna.Framework;
using Microsoft.Xna.Framework.Graphics;
namespace TuneBlaster_
{


    // Author Ahmed Warreth

    // namespace ParticleSample

    /// <summary>
    /// specialization of ParticleSystem which creates a
    /// fiery explosion.combined with  ExplosionSmokeParticleSystem for
    /// best effect.
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
        /// give this particle system its behavior and
        /// properties.
        /// </summary>
        protected override void InitializeConstants()
        {



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








            minInitialSpeed = 40;
            maxInitialSpeed = 500;

            minAcceleration = 0;
            maxAcceleration = 0;

            //short life
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



            if (textureFilename == "null" )
            {




                // less initial speed than the explosion itself
                minInitialSpeed = 20;
                maxInitialSpeed = 200;

                // acceleration is negative, so particles will accelerate away from the
                // initial velocity.  this will make them slow down, as if from wind
                // resistance. we want the smoke to linger a bit and feel wispy, though,
                // so we don't stop them completely like we do ExplosionParticleSystem
                // particles.
                minAcceleration = -10;
                maxAcceleration = -50;

                // explosion smoke lasts for longer than the explosion itself, but not
                // as long as the plumes do.
               // minLifetime = 1.0f;
                //maxLifetime = 2.5f;

                //minScale = 1.0f;
                //maxScale = 2.0f;

                //minNumParticles = 10;
               // maxNumParticles = 20;


                minLifetime = 1.0f;
                maxLifetime = 1.5f;

                minScale = 1.0f;
                maxScale = 2.0f;

                minNumParticles = 5;
                maxNumParticles = 10;


                //  minRotationSpeed = -MathHelper.PiOver4;
                // maxRotationSpeed = MathHelper.PiOver4;

                // spriteBlendMode = SpriteBlendMode.AlphaBlend;

                // DrawOrder = AlphaBlendDrawOrder;




            }





        }

        private void LoadGraphicsContent(SpriteBatch SpriteBatch, object texture)
        {
            throw new Exception("The method or operation is not implemented.");
        }





        protected override void InitializeParticle(Particle p, Vector2 where)
        {
            base.InitializeParticle(p, where);

            // The base works fine except for acceleration. Explosions move outwards,
            // then slow down and stop because of air resistance. Let's change
            // acceleration so that when the particle is at max lifetime, the velocity
            // will be zero.

            // We'll use the equation vt = v0 + (a0 * t). (If you're not familar with
            // this, it's one of the basic kinematics equations for constant
            // acceleration, and basically says:
            // velocity at time t = initial velocity + acceleration * t)
            // We'll solve the equation for a0, using t = p.Lifetime and vt = 0.
            p.Acceleration = -p.Velocity / p.Lifetime;
        }
    }
}


























