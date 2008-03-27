using System.IO;
using Microsoft.Xna.Framework;
using System;
using Drought.GameStates;

namespace Drought.World
{
    public class HeightMap
    {
        float[,] map;
        Level level;

        int width, height;

        public HeightMap(Level theLevel)
        {
            level = theLevel;

            initalise();
        }

        public HeightMap(int width, int height)
        {
            this.width = width;
            this.height = height;

            map = new float[width, height];
        }

        public void initalise()
        {
            string fileName;
            switch (level) {
                case Level.Valley: fileName = "level_0"; break;
                case Level.Rugged: fileName = "level_1"; break;
                case Level.RuggedSplitTextures: fileName = "level_2"; break;
                case Level.Square: fileName = "square"; break;
                case Level.WaterTest: fileName = "water"; break;
                default: fileName = "level_1"; break;
            }
            FileStream fs = new FileStream("Content/HeightMaps/"+fileName+".bmp", FileMode.Open, FileAccess.Read);
            BinaryReader r = new BinaryReader(fs);

            r.BaseStream.Seek(10, SeekOrigin.Current);
            int bitmapOffset = (int)r.ReadUInt32();

            r.BaseStream.Seek(4, SeekOrigin.Current);
            width = (int)r.ReadUInt32();
            height = (int)r.ReadUInt32();

            map = new float[width, height];

            r.BaseStream.Seek(bitmapOffset - 26, SeekOrigin.Current);
            for (int x = 0; x < height; x++)
            {
                for (int y = 0; y < width; y++)
                {
                    int currHeight = (int)r.ReadByte();
                    currHeight += r.ReadByte();
                    currHeight += r.ReadByte();
                    currHeight /= 8;

                    map[width - y - 1, height - x - 1] = currHeight;
                }
            }
            r.Close();
        }

        private float distanceFromALine(float pX, float pY, float lX0, float lY0, float lX1, float lY1)
        {
            Vector2 n = Vector2.Normalize(new Vector2(lX0 - lX1, lY0 - lY1));
            Vector2 v = new Vector2(pX - lX0, pY - lY0);
            return Math.Abs(Vector2.Dot(new Vector2(-n.Y, n.X), v));
        }

        public int getMapWidth()
        {
            return width;
        }

        public int getMapHeight()
        {
            return height;
        }

        public float getHeight(float x, float y)
        {
            int x1 = (int)x;
            int x2 = x1 + 1;
            int y1 = (int)y;
            int y2 = y1 + 1;
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
                return map[(int)x, (int)y];


            if (x - x1 == 0.0f && y - y1 == 0.0f)
                return map[(int)x, (int)y];


            if ((x - (int)x) + (y - (int)y) > 1.0f)
            {
                float alpha = distanceFromALine(x, y, x1, y2, x2, y1) / distanceFromALine(x2, y2, x1, y2, x2, y1);
                float beta = distanceFromALine(x, y, x2, y1, x2, y2);
                float gamma = distanceFromALine(x, y, x2, y2, x1, y2);

                float returnValue = alpha * map[x2, y2] + beta * map[x1, y2] + gamma * map[x2, y1];

                return returnValue;
            }
            else
            {
                float alpha = distanceFromALine(x, y, x1, y2, x2, y1) / distanceFromALine(x1, y1, x1, y2, x2, y1);
                float beta = distanceFromALine(x, y, x2, y1, x1, y1);
                float gamma = distanceFromALine(x, y, x1, y1, x1, y2);

                float returnValue = alpha * map[x1, y1] + beta * map[x1, y2] + gamma * map[x2, y1];

                return returnValue;
            }
        }

        public void setHeight(float x, float y, float height)
        {
            map[(int)x, (int)y] = height;
        }

        public HeightMap clone()
        {
            HeightMap heightMap = new HeightMap(width, height);
            for (int x = 0; x < width; x++)
                for (int y = 0; y < height; y++)
                    heightMap.setHeight(x, y, map[x, y]);

            return heightMap;
        }

    }
}
