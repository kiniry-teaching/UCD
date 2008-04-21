#region File Description
//-----------------------------------------------------------------------------
// Projectile.cs
//
// Microsoft XNA Community Game Platform
// Copyright (C) Microsoft Corporation. All rights reserved.
//-----------------------------------------------------------------------------
#endregion

#region Using Statements
using System;
using Microsoft.Xna.Framework;
using Drought.Entity;
using System.Collections.Generic;
#endregion

namespace Drought.Graphics.Particles
{
    /// <summary>
    /// This class demonstrates how to combine several different particle systems
    /// to build up a more sophisticated composite effect. It implements a rocket
    /// projectile, which arcs up into the sky using a ParticleEmitter to leave a
    /// steady stream of trail particles behind it. After a while it explodes,
    /// creating a sudden burst of explosion and smoke particles.
    /// </summary>
    class Projectile
    {
        #region Constants

        const float trailParticlesPerSecond = 200;
        const int numExplosionParticles = 30;
        const int numExplosionSmokeParticles = 0;
        const float projectileLifespan = 1.5f;
        const float sidewaysVelocityRange = 60;
        const float verticalVelocityRange = 40;
        //const float gravity = 15;

        #endregion

        #region Fields

        ParticleSystem explosionParticles;
        ParticleSystem explosionSmokeParticles;
        ParticleEmitter trailEmitter;

        Vector3 position;
        Vector3 target;
        MovableEntity targetEntity;
        Path myPath;

        #endregion


        /// <summary>
        /// Constructs a new projectile.
        /// </summary>
        public Projectile(ParticleSystem explosionParticles, ParticleSystem explosionSmokeParticles, ParticleSystem projectileTrailParticles, MovableEntity origin, MovableEntity aTarget)
        {
            this.explosionParticles = explosionParticles;
            this.explosionSmokeParticles = explosionSmokeParticles;

            // Start at the origin, firing in a random (but roughly upward) direction.
            position = origin.getPosition();
            target = aTarget.getPosition();
            targetEntity = aTarget;

            //velocity.X = (float)(random.NextDouble() - 0.5) * sidewaysVelocityRange;
            //velocity.Y = (float)(random.NextDouble() - 0.5) * sidewaysVelocityRange;
            //velocity.Z = (float)(random.NextDouble() + 0.5) * verticalVelocityRange;

            double step = Math.PI / 60;
            //Vector3 mid = (aTarget + aPosition) / 2;
            float radius = Math.Abs(Vector3.Distance(target, position) / 2);
            List<Vector3> path = new List<Vector3>();
            for (int i = 0; i <= 60; i++)
            {
                float thisX = MathHelper.Lerp(position.X, target.X, ((float)i) / 60);
                float thisY = MathHelper.Lerp(position.Y, target.Y, ((float)i) / 60);
                float thisZ = MathHelper.Lerp(position.Z, target.Z, ((float)i) / 60) + radius * (float)Math.Cos(step*(i - 30));
                path.Add(new Vector3(thisX, thisY, thisZ));
            }
            myPath = new Path(path);

            // Use the particle emitter helper to output our trail particles.
            trailEmitter = new ParticleEmitter(projectileTrailParticles, trailParticlesPerSecond, position);
        }


        /// <summary>
        /// Updates the projectile.
        /// </summary>
        public bool Update(GameTime gameTime)
        {
            float elapsedTime = (float)gameTime.ElapsedGameTime.TotalSeconds;

            myPath.addDistance(1);
            position = myPath.getPosition();

            // Update the particle emitter, which will create our particle trail.
            trailEmitter.Update(gameTime, position);

            // If enough time has passed, explode! Note how we pass our velocity
            // in to the AddParticle method: this lets the explosion be influenced
            // by the speed and direction of the projectile which created it.
            if (myPath.isFinished())
            {
                if (Vector3.Distance(targetEntity.getPosition(), target) < 10.0f) targetEntity.hurt(1);
                for (int i = 0; i < numExplosionParticles; i++)
                    explosionParticles.AddParticle(position, new Vector3());

                for (int i = 0; i < numExplosionSmokeParticles; i++)
                    explosionSmokeParticles.AddParticle(position, new Vector3());

                return false;
            }

            return true;
        }
    }
}
