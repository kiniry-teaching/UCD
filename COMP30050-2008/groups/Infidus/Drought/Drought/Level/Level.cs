using System;
using System.Collections.Generic;
using System.Text;

namespace Drought.Level
{
    class Level
    {
        Terrain terrain;
        HeightMap heightMap;
        TextureMap textureMap;

        public Level(Game game, Effect effect, string fileName)
        {
            heightMap = new HeightMap(fileName);
            textureMap = new TextureMap(fileName);

            terrain = new Terrain(game, effect, heightMap, textureMap);
        }
    }
}
