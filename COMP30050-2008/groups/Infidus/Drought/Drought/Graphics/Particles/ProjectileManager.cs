using System.Collections.Generic;
using Microsoft.Xna.Framework;

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

        public void addProjectile(Vector3 pos, Vector3 tar)
        {
            projectiles.Add(new Projectile(explosionParticles, explosionSmokeParticles, projectileTrailParticles, pos, tar));
        }

        public void update(GameTime gameTime)
        {
            for (int i = 0; i < projectiles.Count; i++)
                if (!projectiles[i].Update(gameTime))
                    projectiles.RemoveAt(i--);
        }
	}
}
