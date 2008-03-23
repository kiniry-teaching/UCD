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
        public class ExplosionParticleSystem : ParticleSystem
        {
            public ExplosionParticleSystem(Engine game, int howManyEffects)
                : base(game, howManyEffects)
            {
            }

            /// <summary>
            /// give this particle system its behavior and
            /// properties.
            /// </summary>
            protected override void InitializeConstants()
            {
                textureFilename = "explosion";
                

              
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
























    

