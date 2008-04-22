using Drought.Graphics;
using Drought.State;
using Drought.World;

namespace Drought.Entity
{
    class Scout : MovableEntity
    {
        public static readonly float SPEED = 1.0f;

        public static readonly float RADIUS = 1.5f;

        public static readonly int FULL_HEALTH = 5;

        public static readonly int WATER_CAPACITY = 4000;

        public static readonly int WATER_SUCK_AMOUNT = WATER_CAPACITY / 600;

        public static readonly int WATER_RADIUS = (int)RADIUS + 10;

        public Scout(GameState gameState, LevelInfo levelInfo, ModelLoader modelLoader, Path path, int uid) :
            base(gameState, levelInfo, modelLoader.getModel3D(modelType.Car), path, uid, SPEED, RADIUS, FULL_HEALTH, WATER_CAPACITY, WATER_SUCK_AMOUNT, WATER_RADIUS) { }

        public override void update()
        {
            base.update();
            suckTehWaterz();
        }
    }
}
