using System;
using System.Collections.Generic;
using System.Text;
using Microsoft.Xna.Framework;

namespace Drought.World
{
    class WaterMap
    {
        private HeightMap waterMap;
        private HeightMap heightMap;
        private TextureMap textureMap;

        public WaterMap(HeightMap heightMap, TextureMap textureMap)
        {
            this.heightMap = heightMap;
            this.textureMap = textureMap;

            waterMap = heightMap.clone();
        }

        public void addWater(int water)
        {
            for (int x = 0; x < waterMap.getMapWidth(); x++)
                for (int y = 0; y < waterMap.getMapHeight(); y++)
                {
                    waterMap.setHeight(x, y, waterMap.getHeight(x, y) + water);
                    textureMap.setValue(x, y, new Vector4(1, 0, 0, 0));
                }
        }
    }
}
