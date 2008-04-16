using Drought.Graphics;
using Drought.State;
using Drought.World;

namespace Drought.Entity
{
    class Tanker : MovableEntity
    {
        private const float VELOCITY = 0.3f;

        private const float RADIUS = 2.5f;

        private const int FULL_HEALTH = 15;

        private const int WATER_CAPACITY = 10;

        private const float MODEL_SCALE = 0.1f;


        public Tanker(GameState gameState, Model3D model, Path path, Terrain terrain, int uid) :
            base(gameState, model, path, terrain, uid)
        {
            setVelocity(VELOCITY);
            setRadius(RADIUS);
            setMaxHealth(FULL_HEALTH);
            setMaxWater(WATER_CAPACITY);
            setModelScale(MODEL_SCALE);
        }
    }
}
