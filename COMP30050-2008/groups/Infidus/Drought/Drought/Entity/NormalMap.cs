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

       /**
        * Gets the distance from a point to a line.
        * Distance will be negative if point lies to the left
        * of the line, positive if it lies to the right and 
        * zero if it is on the line.
        *
        * @param line1 First point on the line segment.
        * @param line2 Last point on the line segment.
        * @param p The point to find the distance to.
        */
        public float Distance(Vector3 line1, Vector3 line2, Vector3 p)
        {
            float distance = 0.0f;

            Vector3 v = line1 - p;
            Vector3 n = (line2 - line1);
            float x = n.X;
            float y = n.Y;
            n.X = -y;
            n.Y = x;
            n.Z = 0.0f;
            distance = (Vector3.Dot(n, v) / n.Length());

            return distance;
        }
    }
}
