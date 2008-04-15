using System;
using System.Collections.Generic;
using System.Text;
using Microsoft.Xna.Framework;
using System.IO;

namespace Drought.World
{
    public class LevelInfo
    {
        /** The width of the level. */
        private int width;

        /** The height of the level. */
        private int height;

        /** Map of the level's normals. [x][y][triangle] */
        private Vector3[,,] normals;

        /** Map of the level's heights. [x][y] */
        private float[,] heightMap;

        /** Map of the level's textures. [x][y] */
        private Vector4[,] textureMap;



        #region Initialising methods
        /**
         * Initialises the level information from file.
         */
        public void initialise(String level)
        {
            initHeightMap(level);
            initNormalMap();
            initTextureMap(level);
        }

        /**
         * Initialise the height map from file.
         * 
         * @param fileName The name of the height map file without the extension.
         */
        private void initHeightMap(String fileName)
        {
            FileStream fs = new FileStream("Content/HeightMaps/" + fileName + ".bmp", FileMode.Open, FileAccess.Read);
            BinaryReader r = new BinaryReader(fs);

            r.BaseStream.Seek(10, SeekOrigin.Current);
            int bitmapOffset = (int)r.ReadUInt32();

            r.BaseStream.Seek(4, SeekOrigin.Current);
            width = (int)r.ReadUInt32();
            height = (int)r.ReadUInt32();

            heightMap = new float[width, height];

            r.BaseStream.Seek(bitmapOffset - 26, SeekOrigin.Current);
            for (int x = 0; x < height; x++)
            {
                for (int y = 0; y < width; y++)
                {
                    int currHeight = (int)r.ReadByte();
                    currHeight += r.ReadByte();
                    currHeight += r.ReadByte();
                    currHeight /= 8;

                    heightMap[width - y - 1, height - x - 1] = currHeight;
                }
            }
            r.Close();

            for (int x = 1; x < width - 2; x++)
            {
                for (int y = 1; y < height - 2; y++)
                {
                    heightMap[x, y] = (heightMap[x - 1, y - 1] + heightMap[x - 1, y] + heightMap[x - 1, y + 1] +
                                heightMap[x, y - 1] + heightMap[x, y] + heightMap[x, y + 1] +
                                heightMap[x + 1, y - 1] + heightMap[x + 1, y] + heightMap[x + 1, y + 1]) / 9;
                }
            }
        }

        /**
         * Initialise the normal map. This must be done after the height map has
         * been initialised.
         */
        private void initNormalMap()
        {
            /* each square region is made up of two triangles. */
            normals = new Vector3[width, height, 2];

            for (int x = 0; x < width; x++)
                for (int y = 0; y < height; y++)
                {
                    Vector3 p0 = getPositionAt(x, y);
                    Vector3 p1 = getPositionAt(x + 1, y);
                    Vector3 p2 = getPositionAt(x, y + 1);
                    Vector3 p3 = getPositionAt(x + 1, y + 1);

                    Vector3 v0 = p2 - p0;
                    Vector3 v1 = p3 - p2;
                    Vector3 v2 = p3 - p1;
                    Vector3 v3 = p1 - p0;

                    normals[x, y, 0] = Vector3.Cross(v1, v0);
                    normals[x, y, 1] = Vector3.Cross(v3, v2);
                }
        }

        /**
         * Initialise the texture map from file.
         * 
         * @param fileName The name of the texture map file without the extension.
         */
        private void initTextureMap(String fileName)
        {
            FileStream fs = new FileStream("Content/TextureMaps/" + fileName + ".bmp", FileMode.Open, FileAccess.Read);
            BinaryReader r = new BinaryReader(fs);

            r.BaseStream.Seek(10, SeekOrigin.Current);
            int bitmapOffset = (int)r.ReadUInt32();

            r.BaseStream.Seek(4, SeekOrigin.Current);
            width = (int)r.ReadUInt32();
            height = (int)r.ReadUInt32();

            textureMap = new Vector4[width, height];

            r.BaseStream.Seek(bitmapOffset - 26, SeekOrigin.Current);

            Vector4 textureWeights;
            for (int x = 0; x < height; x++)
            {
                for (int y = 0; y < width; y++)
                {
                    int blueValue = (int)r.ReadByte();
                    int greenValue = (int)r.ReadByte();
                    int redValue = (int)r.ReadByte();

                    textureWeights = Vector4.Normalize(new Vector4(blueValue, redValue, greenValue, 0));

                    textureMap[width - y - 1, height - x - 1] = textureWeights;
                }
            }
            r.Close();
        }
        #endregion

        #region public getter methods
        /**
         * Gets the width of the level.
         * 
         * @return Level's width.
         */
        public int getWidth()
        {
            return width;
        }

        /**
         * Gets the height of the level.
         * 
         * @return Level's height.
         */
        public int getHeight()
        {
            return height;
        }

        /**
         * Gets the height at a specific point in the level by performing
         * a lookup in the height map. If the location provided is out of 
         * range then 0 is returned.
         * 
         * @param x x coordinate of the location to get height at.
         * @param y y coordinate of the location to get height at.
         * @return Height at x, y.
         */
        public float getHeight(int x, int y)
        {
            if (x >= 0 && x < width && y >= 0 && y < height)
                return heightMap[x, y];
            return 0.0f;
        }

        /**
         * Gets the interpolated height at a specified point in the level.
         * If the location given is out of bounds, then the height at the 
         * closest valid position is returned.
         * 
         * @param x x coordinate of the location to get height at.
         * @param y y coordinate of the location to get height at.
         * @return Height at x, y.
         */
        public float getHeight(float x, float y)
        {
            bool outOfBounds = false;

            if (x >= width - 1)
            {
                x = width - 1;
                outOfBounds = true;
            }
            else if (x < 0)
            {
                x = 0;
                outOfBounds = true;
            }
            if (y >= height - 1)
            {
                y = height - 1;
                outOfBounds = true;
            }
            else if (y < 0)
            {
                y = 0;
                outOfBounds = true;
            }
            if (outOfBounds)
                return heightMap[(int)x, (int)y];


            int x1 = (int)x;
            int x2 = x1 + 1;
            int y1 = (int)y;
            int y2 = y1 + 1;

            if (x - x1 == 0.0f && y - y1 == 0.0f)
                return heightMap[(int)x, (int)y];


            if ((x - (int)x) + (y - (int)y) > 1.0f)
            {
                float alpha = distanceFromALine(x, y, x1, y2, x2, y1) / distanceFromALine(x2, y2, x1, y2, x2, y1);
                float beta = distanceFromALine(x, y, x2, y1, x2, y2);
                float gamma = distanceFromALine(x, y, x2, y2, x1, y2);

                float returnValue = alpha * heightMap[x2, y2] + beta * heightMap[x1, y2] + gamma * heightMap[x2, y1];

                return returnValue;
            }
            else
            {
                float alpha = distanceFromALine(x, y, x1, y2, x2, y1) / distanceFromALine(x1, y1, x1, y2, x2, y1);
                float beta = distanceFromALine(x, y, x2, y1, x1, y1);
                float gamma = distanceFromALine(x, y, x1, y1, x1, y2);

                float returnValue = alpha * heightMap[x1, y1] + beta * heightMap[x1, y2] + gamma * heightMap[x2, y1];

                return returnValue;
            }
        }

        /**
         * Gets the height at a specified point in the level and returns it
         * in a vector width its x and y values set to the given location.
         * If the location given is out of bounds, then the height at the 
         * closest valid position is returned.
         * 
         * @param x x coordinate of the location to get height at.
         * @param y y coordinate of the location to get height at.
         * @return Vector3 containing the height at x, y.
         */
        public Vector3 getPositionAt(float x, float y)
        {
            return new Vector3(x, y, getHeight(x, y));
        }

        /**
         * Gets the normal at the specified location.
         * If the location is out of bounds then a Vector3 with
         * all its values initialised to 0 is returned.
         * 
         * @param x x coordinate of the location to get normal at.
         * @param y y coordinate of the location to get normal at.
         * @return Vector3 containing the normal at x, y.
         */
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
         * Gets the texture value at the specified location.
         * If the location is out of bounds a Vector4 with all its
         * components initialised to 0 is returned.
         * 
         * @param x x coordinate of the location to get texture value at.
         * @param y y coordinate of the location to get texture value at.
         * @return Vector3 containing the texture value at x, y.
         */
        public Vector4 getTextureValue(float x, float y)
        {
            if(x >= 0 && x < width && y >= 0 && y < height)
                return textureMap[(int)x, (int)y];
            return new Vector4(0, 0, 0, 0);
        }
        #endregion

        #region private helper methods

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
        private static float distance(float line1x, float line1y, float line2x, float line2y, float px, float py)
        {
            float distance = 0.0f;

            Vector2 v = new Vector2(line1x - px, line1y - py);
            Vector2 n = new Vector2(line2x - line1x, line2y - line1y);
            float x = n.X;
            float y = n.Y;
            n.X = -y;
            n.Y = x;
            distance = (Vector2.Dot(n, v) / n.Length());

            return distance;
        }

        private static float distanceFromALine(float pX, float pY, float lX0, float lY0, float lX1, float lY1)
        {
            Vector2 n = Vector2.Normalize(new Vector2(lX0 - lX1, lY0 - lY1));
            Vector2 v = new Vector2(pX - lX0, pY - lY0);
            return Math.Abs(Vector2.Dot(new Vector2(-n.Y, n.X), v));
        }

        #endregion
    }
}
