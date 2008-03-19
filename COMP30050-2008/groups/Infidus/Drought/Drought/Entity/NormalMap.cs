using System;
using System.Collections.Generic;
using System.Text;
using Drought.World;
using Microsoft.Xna.Framework;

namespace Drought.Entity
{
    public class NormalMap
    {
        private Vector3[,,] normals;

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
            normals = new Vector3[width, height, 2];

            for (int x = 0; x < width; x++)
                for (int y = 0; y < height; y++)
                {
                    Vector3 p0 = new Vector3(x, y, heightMap.getHeight(x, y));
                    Vector3 p1 = new Vector3(x + 1, y, heightMap.getHeight(x + 1, y));
                    Vector3 p2 = new Vector3(x, y + 1, heightMap.getHeight(x, y + 1));
                    Vector3 p3 = new Vector3(x + 1, y + 1, heightMap.getHeight(x + 1, y + 1));

                    Vector3 v0 = p2 - p0;
                    Vector3 v1 = p3 - p2;
                    Vector3 v2 = p3 - p1;
                    Vector3 v3 = p1 - p0;

                    normals[x, y, 0] = Vector3.Cross(v1, v0);
                    normals[x, y, 1] = Vector3.Cross(v3, v2);
                }
        }

        public Vector3 getNormal(float x, float y)
        {
            if (x >= 0 && x < width && y >= 0 && y < height)
            {
                int ix = (int)x;
                int iy = (int)y;

                if (distance(ix, iy, ix + 1, iy + 1, x, y) < 0.0f
                    && distance(ix + 1, iy + 1, ix + 1, iy, x, y) < 0.0f
                    && distance(ix + 1, iy, ix, iy, x, y) < 0.0f)
                {
                    return normals[ix, iy, 1];
                }

                return normals[ix, iy, 0];
            }

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
        public float distance(Vector3 line1, Vector3 line2, Vector3 p)
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

        /**
        * Gets the distance from a point to a line.
        * Distance will be negative if point lies to the left
        * of the line, positive if it lies to the right and 
        * zero if it is on the line.
        *
        * @param line1x x coordinate of the first point on the line segment.
        * @param line1y y coordinate of the first point on the line segment.
        * @param line2x x coordinate of the last point on the line segment.
        * @param line2y y coordinate of the last point on the line segment.
        * @param px x coordinate of the point to find the distance to.
        * @param py y coordinate of the point to find the distance to.
        */
        public float distance(float line1x, float line1y , float line2x, float line2y, float px, float py)
        {
            float distance = 0.0f;

            Vector2 v = new Vector2(line1x - px, line1y - py);
            Vector2 n = new Vector2(line2x - line1x, line2y - line1y);
            float x = n.X;
            float y = n.Y;
            n.X = -y;
            n.Y = x;
            distance = (Vector2.Dot(n , v) / n.Length());

            return distance;
        }
    }
}
