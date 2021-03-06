using System.IO;
using Microsoft.Xna.Framework;
using Drought.GameStates;
using System.Collections.Generic;
using System;

namespace Drought.World
{
    class TextureMap
    {
        /** For depth first search; indicates that there is no path onward from the provided node. */
        private static readonly Vector3 DEAD_END = new Vector3(float.PositiveInfinity);

        /** How much water texture weight a point must have to be considered "water". */
        private static readonly float WATER_THRESHOLD = 0.3f;

        private bool[,] waterMap;

        private Vector4[,] map;
        private int width, height;

        private Level level;
        private bool changed;
        public bool Changed { get { return changed; } }

        public TextureMap(Level theLevel)
        {
            level = theLevel;
            changed = false;

            initialise();
        }

        public void initialise()
        {
            string fileName = LevelInfo.getFileName(level);

            FileStream fs = new FileStream("Content/TextureMaps/" + fileName + ".bmp", FileMode.Open, FileAccess.Read);
            BinaryReader r = new BinaryReader(fs);

            r.BaseStream.Seek(10, SeekOrigin.Current);
            int bitmapOffset = (int)r.ReadUInt32();

            r.BaseStream.Seek(4, SeekOrigin.Current);
            width = (int)r.ReadUInt32();
            height = (int)r.ReadUInt32();

            map = new Vector4[width, height];

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

                    map[width - y - 1, height - x - 1] = textureWeights;
                }
            }
            r.Close();
        }

        public Vector4 getValue(float x, float y)
        {
            return map[(int)x, (int)y];
        }

        public void setValue(float x, float y, Vector4 value)
        {
            map[(int)x, (int)y] = value;
            changed = true;
        }

        public List<List<Vector3>> findWater()
        {
            List<List<Vector3>> waterPoints = new List<List<Vector3>>();
            waterMap = new bool[width, height];
            for (int x = 0; x < width; x++)
            {
                for (int y = 0; y < height; y++)
                {
                    if (!waterMap[x, y] && isEdge(x, y))
                    {
                        waterMap[x, y] = true;
                        List<Vector3> edgePoints = depthFirstSearch(new Vector3(x, y, 0), new Vector3(x + 1, y, 0));
                        if (edgePoints.Count > 0)
                        {
                            edgePoints.Reverse();
                            waterPoints.Add(edgePoints);
                        }
                    }
                }
            }
            return waterPoints;
        }

        private List<Vector3> depthFirstSearch(Vector3 start, Vector3 end)
        {
            List<Vector3> edgePoints = new List<Vector3>();
            depthFirstSearch(start, end, edgePoints);
            return edgePoints;
        }

        private Vector3 depthFirstSearch(Vector3 curr, Vector3 goal, List<Vector3> path)
        {
            if (curr.Equals(goal))
            {
                path.Add(goal);
                return goal;
            }

            Vector3 newPoint;
            if (curr.X > 0 && curr.Y > 0 && !waterMap[(int)curr.X - 1, (int)curr.Y - 1] && isEdge((int)curr.X - 1, (int)curr.Y - 1))
            {
                waterMap[(int)curr.X - 1, (int)curr.Y - 1] = true;
                newPoint = new Vector3((int)curr.X - 1, (int)curr.Y - 1, 0);
                if (!depthFirstSearch(newPoint, goal, path).Equals(DEAD_END))
                {
                    path.Add(curr);
                    return curr;
                }
            }

            if (curr.X > 0 && !waterMap[(int)curr.X - 1, (int)curr.Y] && isEdge((int)curr.X - 1, (int)curr.Y))
            {
                waterMap[(int)curr.X - 1, (int)curr.Y] = true;
                newPoint = new Vector3((int)curr.X - 1, (int)curr.Y, 0);
                if (!depthFirstSearch(newPoint, goal, path).Equals(DEAD_END))
                {
                    path.Add(curr);
                    return curr;
                }
            }

            if (curr.X > 0 && curr.Y < height - 1 && !waterMap[(int)curr.X - 1, (int)curr.Y + 1] && isEdge((int)curr.X - 1, (int)curr.Y + 1))
            {
                waterMap[(int)curr.X - 1, (int)curr.Y + 1] = true;
                newPoint = new Vector3((int)curr.X - 1, (int)curr.Y + 1, 0);
                if (!depthFirstSearch(newPoint, goal, path).Equals(DEAD_END))
                {
                    path.Add(curr);
                    return curr;
                }
            }

            if (curr.Y < height - 1 && !waterMap[(int)curr.X, (int)curr.Y + 1] && isEdge((int)curr.X, (int)curr.Y + 1))
            {
                waterMap[(int)curr.X, (int)curr.Y + 1] = true;
                newPoint = new Vector3((int)curr.X, (int)curr.Y + 1, 0);
                if (!depthFirstSearch(newPoint, goal, path).Equals(DEAD_END))
                {
                    path.Add(curr);
                    return curr;
                }
            }

            if (curr.Y > 0 && !waterMap[(int)curr.X, (int)curr.Y - 1] && isEdge((int)curr.X, (int)curr.Y - 1))
            {
                waterMap[(int)curr.X, (int)curr.Y - 1] = true;
                newPoint = new Vector3((int)curr.X, (int)curr.Y - 1, 0);
                if (!depthFirstSearch(newPoint, goal, path).Equals(DEAD_END))
                {
                    path.Add(curr);
                    return curr;
                }
            }

            if (curr.X < width - 1 && curr.Y < height - 1 && !waterMap[(int)curr.X + 1, (int)curr.Y + 1] && isEdge((int)curr.X + 1, (int)curr.Y + 1))
            {
                waterMap[(int)curr.X + 1, (int)curr.Y + 1] = true;
                newPoint = new Vector3((int)curr.X + 1, (int)curr.Y + 1, 0);
                if (!depthFirstSearch(newPoint, goal, path).Equals(DEAD_END))
                {
                    path.Add(curr);
                    return curr;
                }
            }

            if (curr.X < width - 1 && curr.Y > 0 && !waterMap[(int)curr.X + 1, (int)curr.Y - 1] && isEdge((int)curr.X + 1, (int)curr.Y - 1))
            {
                waterMap[(int)curr.X + 1, (int)curr.Y - 1] = true;
                newPoint = new Vector3((int)curr.X + 1, (int)curr.Y - 1, 0);
                if (!depthFirstSearch(newPoint, goal, path).Equals(DEAD_END))
                {
                    path.Add(curr);
                    return curr;
                }
            }

            if (curr.X < width - 1 && !waterMap[(int)curr.X + 1, (int)curr.Y] && isEdge((int)curr.X + 1, (int)curr.Y))
            {
                waterMap[(int)curr.X + 1, (int)curr.Y] = true;
                newPoint = new Vector3((int)curr.X + 1, (int)curr.Y, 0);
                if (!depthFirstSearch(newPoint, goal, path).Equals(DEAD_END))
                {
                    path.Add(curr);
                    return curr;
                }
            }

            return DEAD_END;
        }

        private bool isEdge(int x, int y)
        {
            if (map[x, y].X >= WATER_THRESHOLD)
            {
                if (y > 0)
                {
                    if (map[x, y - 1].X < WATER_THRESHOLD)
                    {
                        return true;
                    }

                    if (x > 0)
                    {
                        if (map[x - 1, y - 1].X < WATER_THRESHOLD || map[x - 1, y].X < WATER_THRESHOLD)
                        {
                            return true;
                        }
                    }
                    else
                    {
                        return true;
                    }


                    if (x < width - 1)
                    {
                        if (map[x + 1, y - 1].X < WATER_THRESHOLD || map[x + 1, y].X < WATER_THRESHOLD)
                        {
                            return true;
                        }
                    }
                    else
                    {
                        return true;
                    }

                }
                else
                {
                    return true;
                }

                if (y < height - 1)
                {
                    if (map[x, y + 1].X < WATER_THRESHOLD)
                    {
                        return true;
                    }

                    if (x > 0)
                    {
                        if (map[x - 1, y + 1].X < WATER_THRESHOLD)
                        {
                            return true;
                        }
                    }
                    else
                    {
                        return true;
                    }


                    if (x < width - 1)
                    {
                        if (map[x + 1, y + 1].X < WATER_THRESHOLD)
                        {
                            return true;
                        }
                    }
                    else
                    {
                        return true;
                    }

                }
                else
                {
                    return true;
                }
            }
            return false;
        }
    }
}
