using Drought.Graphics;
using Drought.State;
using Drought.World;

namespace Drought.Entity
{
    class Tanker : MovableEntity
    {
        public static readonly float SPEED = 0.3f;

        public static readonly float RADIUS = 2.5f;

        public static readonly int FULL_HEALTH = 15;

        public static readonly int WATER_CAPACITY = 10000;

        public static readonly int WATER_SUCK_AMOUNT = WATER_CAPACITY / 600;

        public static readonly int WATER_RADIUS = (int)RADIUS + 5;

        public Tanker(GameState gameState, LevelInfo levelInfo, ModelLoader modelLoader, Path path, int uid) :
            base(gameState, levelInfo, modelLoader.getModel3D(modelType.Truck), path, uid, SPEED, RADIUS, FULL_HEALTH, WATER_CAPACITY, WATER_SUCK_AMOUNT, WATER_RADIUS) { }

        public override void update()
        {
            base.update();
            suckTehWaterz();
        }   
    }
}
