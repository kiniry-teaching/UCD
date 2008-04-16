using Drought.Graphics;
using Drought.State;
using Drought.World;

namespace Drought.Entity
{
    class Guard : MovableEntity
    {
        private const float VELOCITY = 0.4f;

        private const float RADIUS = 2.0f;

        private const int FULL_HEALTH = 10;

        private const int WATER_CAPACITY = 0;

        private const float MODEL_SCALE = 0.05f;

        private const float ATTACK_RADIUS = 10.0f;


        public Guard(GameState gameState, Model3D model, Path path, Terrain terrain, int uid) :
            base(gameState, model, path, terrain, uid)
        {
            setVelocity(VELOCITY);
            setRadius(RADIUS);
            setMaxHealth(FULL_HEALTH);
            setMaxWater(WATER_CAPACITY);
            setModelScale(MODEL_SCALE);
        }

        public new void update()
        {
            base.update();

            /* attack logic */

        }
    }
}
