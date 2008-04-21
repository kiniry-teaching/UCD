using System;
using System.Collections.Generic;
using System.Text;
using Microsoft.Xna.Framework;

namespace Drought.Graphics.Particles
{
	class ProjectileManager
	{
        private List<Projectile> projectiles = new List<Projectile>();

        private ParticleSystem explosionParticles;
        private ParticleSystem explosionSmokeParticles;
        private ParticleSystem projectileTrailParticles;

        public ProjectileManager(ParticleSystem explosion, ParticleSystem explosionSmoke, ParticleSystem projectileTrail)
        {
            explosionParticles = explosion;
            explosionSmokeParticles = explosionSmoke;
            projectileTrailParticles = projectileTrail;
        }

        public void addProjectile(Vector3 pos)
        {
            projectiles.Add(new Projectile(explosionParticles, explosionSmokeParticles, projectileTrailParticles, pos));
        }

        public void update(GameTime gameTime)
        {
            for (int i = 0; i < projectiles.Count; i++)
                if (!projectiles[i].Update(gameTime))
                    projectiles.RemoveAt(i--);
        }
	}
}
