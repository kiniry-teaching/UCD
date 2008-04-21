using System.Collections.Generic;
using Microsoft.Xna.Framework;
using Drought.Entity;

namespace Drought.Graphics.Particles
{
	class ProjectileManager
	{
        private List<Projectile> projectiles = new List<Projectile>();

        private ExplosionParticleSystem explosionParticles;
        private ExplosionSmokeParticleSystem explosionSmokeParticles;
        private ProjectileTrailParticleSystem projectileTrailParticles;

        public ProjectileManager(ExplosionParticleSystem explosion, ExplosionSmokeParticleSystem explosionSmoke, ProjectileTrailParticleSystem projectileTrail)
        {
            explosionParticles = explosion;
            explosionSmokeParticles = explosionSmoke;
            projectileTrailParticles = projectileTrail;
        }

        public void addProjectile(MovableEntity org, MovableEntity tar)
        {
            projectiles.Add(new Projectile(explosionParticles, explosionSmokeParticles, projectileTrailParticles, org, tar));
        }

        public void update(GameTime gameTime)
        {
            for (int i = 0; i < projectiles.Count; i++)
                if (!projectiles[i].Update(gameTime))
                    projectiles.RemoveAt(i--);
        }
	}
}
