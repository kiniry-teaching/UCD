using System.Collections.Generic;

namespace Drought.Graphics.Particles
{
    class ExplosionEffect
    {
        private List<ExplosionEffect> callback;

        public ExplosionEffect(List<ExplosionEffect> callback)
        {
            this.callback = callback;
        }

        public void update()
        {
            
        }
    }
}
