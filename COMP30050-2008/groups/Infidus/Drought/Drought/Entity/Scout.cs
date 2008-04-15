using System;
using System.Collections.Generic;
using System.Text;
using Drought.State;
using Microsoft.Xna.Framework.Graphics;
using Drought.World;

namespace Drought.Entity
{
    class Scout : MovableEntity
    {
        private const float VELOCITY = 1.0f;

        private const float RADIUS = 1.5f;

        private const int FULL_HEALTH = 5;

        private const int WATER_CAPACITY = 4;

        private const float MODEL_SCALE = 1.0f;


        public Scout(GameState gameState, Model model, Texture2D[] modelTextures, Path path, Terrain terrain, int uid) :
            base(gameState, model, modelTextures, path, terrain, uid)
        {
            setVecocity(VELOCITY);
            setRadius(RADIUS);
            setMaxHealth(FULL_HEALTH);
            setMaxWater(WATER_CAPACITY);
            setModelScale(MODEL_SCALE);
        }


    }
}
