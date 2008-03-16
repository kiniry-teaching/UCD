using System;
using System.Collections.Generic;
using System.Text;
using Drought.World;
using Microsoft.Xna.Framework;

namespace Drought.Entity
{
    class NormalMap
    {
        private Vector3[,] normals;

        private int width;

        private int height;

        public NormalMap(HeightMap heightMap)
        {
            initialise(heightMap);
        }

        private void initialise(HeightMap heightMap)
        {
            width = heightMap.getMapWidth();
            height = heightMap.getMapHeight();
            normals = new Vector3[width, height];

            for (int x = 0; x < width; x++)
                for (int y = 0; y < height; y++)
                {
                    Vector3 p0 = new Vector3(x, y, heightMap.getHeight(x, y));
                    Vector3 p1 = new Vector3(x + 1, y, heightMap.getHeight(x + 1, y));
                    Vector3 p2 = new Vector3(x, y + 1, heightMap.getHeight(x, y + 1));

                    Vector3 v0 = p1 - p0;
                    Vector3 v1 = p2 - p0;

                    normals[x, y] = Vector3.Cross(v0, v1);
                }
        }

        public Vector3 getNormal(int x, int y)
        {
            if(x >= 0 && x < width && y >= 0 && y < height)
                return normals[x, y];
            return new Vector3(0, 0, 0);
        }
    }
}
