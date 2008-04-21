using System;
using System.Collections.Generic;
using System.Text;
using Microsoft.Xna.Framework;
using Microsoft.Xna.Framework.Graphics;

namespace Drought.World
{
    /** A continuous body of water. */
    class Water
    {
        /** For depth first search; indicates that there is no path onward from the provided node. */
        private static readonly Vector3 DEAD_END = new Vector3(float.PositiveInfinity);

        /** How much water texture weight a point must have to be considered "water". */
        private static readonly float WATER_THRESHOLD = 0.3f;

        //for drawing the water surface
        private VertexPositionColor[] vertices;
        private VertexDeclaration vd;
        private BasicEffect effect;
        
        /** The water in this lake when it was created. */
        private float totalWater;

        /** The water currently remaining. */
        private float currentWater;

        /** The height the water plane was at when the lake was created. */
        private float initialWaterLevel;

        /** The lowest point in the lake. */
        private float bottomWaterLevel;

        public Water(List<Vector3> points, LevelInfo levelInfo, GraphicsDevice graphics)
        {
            initialize(points, levelInfo);
            vd = new VertexDeclaration(graphics, VertexPositionColor.VertexElements);
            effect = new BasicEffect(graphics, null);
        }

        public void initialize(List<Vector3> points, LevelInfo levelInfo)
        {
            Vector3 averageCenter = new Vector3(0, 0, 0);
            float totalDist = 0;
            Vector3 boxCenter = new Vector3(0, 0, 0);
            float xMin = float.MaxValue; int xMinPos = -1; float xMax = float.MinValue; int xMaxPos = -1;
            float yMin = float.MaxValue; int yMinPos = -1; float yMax = float.MinValue; int yMaxPos = -1;
            float zMin = float.MaxValue;
            for (int i = 0; i < points.Count; i++)
            {
                points[i] = new Vector3(points[i].X, points[i].Y, levelInfo.getHeight(points[i].X, points[i].Y) - 0.01f);
                if (points[i].X < xMin) { xMin = points[i].X; xMinPos = i; }
                if (points[i].X > xMax) { xMax = points[i].X; xMaxPos = i; }
                if (points[i].Y < yMin) { yMin = points[i].Y; yMinPos = i; }
                if (points[i].Y > yMax) { yMax = points[i].Y; yMaxPos = i; }
                if (points[i].Z < zMin && notEdgePoint(points[i], levelInfo)) { zMin = points[i].Z; }
                averageCenter += points[i];
                totalDist += Vector3.Distance(points[i], points[(i+1)%points.Count]);
            }
            float zMinInside = zMin;
            for (float i = xMin; i <= xMax; i++) 
                for (float j = yMin; j <= yMax; j++)
                    if (levelInfo.getHeight(i, j) < zMinInside) zMinInside = levelInfo.getHeight(i, j);

            zMinInside -= 0.02f;
            initialWaterLevel = zMin;
            bottomWaterLevel = zMinInside;
            float waterHeight = zMin - zMinInside;

            totalWater = approximateArea(totalDist, waterHeight) / 333.0f;
            currentWater = totalWater;

            averageCenter /= points.Count;
            boxCenter.X = (points[xMinPos].X + points[xMaxPos].X) / 2;
            boxCenter.Y = (points[yMinPos].Y + points[yMaxPos].Y) / 2;
            boxCenter.Z = averageCenter.Z;

            List<Vector3> extremePoints = new List<Vector3>();
            List<Vector3> restPoints = new List<Vector3>();
            for (int i=0; i<points.Count; i++)
            {
                if (i == xMinPos || i == xMaxPos || i == yMinPos || i == yMaxPos) {
                    extremePoints.Add(points[i]);
                }
                else restPoints.Add(points[i]);
            }

            //very broken!
            //List<Vector3> finalPoints = minimumConvexArea(restPoints, extremePoints, boxCenter);
            //working
            List<Vector3> finalPoints = facePointArea(points, averageCenter);

            vertices = new VertexPositionColor[finalPoints.Count + 2];
            vertices[0].Position = averageCenter;
            vertices[0].Position.Z = zMin;
            for (int i = 0; i < finalPoints.Count; i++)
            {
                //vertices[i+1].Position = new Vector3(finalPoints[i].X, finalPoints[i].Y, averageCenter.Z);
                vertices[i + 1].Position = new Vector3(finalPoints[i].X, finalPoints[i].Y, zMin);
            }
            vertices[vertices.Length - 1] = vertices[1];
        }

        private int lastTime = 0;
        public void update(GameTime gameTime)
        {
            //automatic water drainage
            /* 
            int time = (int) gameTime.TotalRealTime.TotalMilliseconds;
            if ( time > lastTime + 20) 
            {
                currentWater -= 100.0f;
                if (currentWater < 0.0f) currentWater = 0.0f;
                setNewWaterLevel();

                lastTime = time;
            }
            */

            setNewWaterLevel();
        }

        public float removeWater(float amt)
        {
            currentWater -= amt;
            float result = amt;

            if (currentWater < 0)
            {
                result += currentWater;
                currentWater = 0;
            }

            return result;
        }

        public void render(GraphicsDevice graphics, Matrix viewMatrix, Matrix projectionMatrix)
        {
            graphics.VertexDeclaration = vd;

            if (vertices.Length > 1)
            {
                graphics.RenderState.AlphaBlendEnable = true;
                graphics.RenderState.SourceBlend = Blend.SourceAlpha;
                graphics.RenderState.DestinationBlend = Blend.InverseSourceAlpha;

                effect.DiffuseColor = Color.LightBlue.ToVector3();
                effect.Alpha = 0.5f;
                effect.World = Matrix.Identity;
                effect.View = viewMatrix;
                effect.Projection = projectionMatrix;

                effect.Begin();
                foreach (EffectPass pass in effect.CurrentTechnique.Passes)
                {
                    pass.Begin();

                    graphics.DrawUserPrimitives<VertexPositionColor>(
                        PrimitiveType.TriangleFan, vertices, 0, vertices.Length - 2);

                    pass.End();
                }
                effect.End();
            }
        }

        /** Takes the remaining water in the lake and sets the height appropriately. */
        private void setNewWaterLevel()
        {
            float scale = currentWater / totalWater;

            for (int i = 0; i < vertices.Length; i++)
            {
                vertices[i].Position.Z = MathHelper.Lerp(bottomWaterLevel, initialWaterLevel, scale);
            }
        }

        /** Takes in the length of the perimeter of a lake, and approximates it's area. */
        public static float approximateArea(float circumference, float height)
        {
            //area of a cone: rough approximation
            return (float)(4 * height * (circumference / 2.0) * (circumference / 2.0) / (3 * Math.PI));
        }

        /** Finds the minimum bounding convex area containing all points in <param name="points">points</param>. */
        /* NOTE: only works if xMin, xMax, yMin and yMax are unique! */
        private List<Vector3> minimumConvexArea(List<Vector3> points, List<Vector3> initialPoints, Vector3 center) {
            List<Vector3> distSortedPoints = new List<Vector3>(points);
            distSortedPoints.Sort(
                delegate(Vector3 v1, Vector3 v2) {
                    return (int) (Vector3.DistanceSquared(center, v1) - Vector3.DistanceSquared(center, v2));
                }
            );

            List<WaterEdge> bounds = new List<WaterEdge>();
            for (int i = 0; i < initialPoints.Count; i++)
            {
                int next = (i + 1) % initialPoints.Count;
                bounds.Add(new WaterEdge(initialPoints[i], initialPoints[next], isClosed(points, center, initialPoints[i], initialPoints[next])));
            }
            int nextSort = 0;
            int firstOpen = 0;
            while (firstOpen < bounds.Count) {
                Vector3 next = distSortedPoints[nextSort++];
                for (int i = firstOpen; i < bounds.Count; i++) {
                    if (bounds[i].isOutside(next)) {
                        WaterEdge edgeA = new WaterEdge(bounds[i].NodeA, next, isClosed(points, center, bounds[i].NodeA, next));
                        WaterEdge edgeB = new WaterEdge(next, bounds[i].NodeB, isClosed(points, center, next, bounds[i].NodeB));
                        bounds.Remove(bounds[i]);
                        bounds.Insert(i, edgeB);
                        bounds.Insert(i, edgeA);
                        if (i == firstOpen) {
                            while (firstOpen < bounds.Count && !bounds[firstOpen].Closed) firstOpen++;
                        }
                        break;
                    }
                }
            }
            List<Vector3> boundPoits = new List<Vector3>(bounds.Count);
            for (int i = 0; i < bounds.Count; i++) {
                boundPoits.Add(bounds[i].NodeA);
            }
            return boundPoits;
        }

        private List<Vector3> isClosed(List<Vector3> points, Vector3 center, Vector3 a, Vector3 b) {
            List<Vector3> outsiders = new List<Vector3>();

            Vector2 n = Vector2.Normalize(new Vector2(a.X - b.X, a.Y - b.Y));
            Vector2 v = new Vector2(center.X - a.X, center.Y - a.Y);
            float dist = Vector2.Dot(new Vector2(-n.Y, n.X), v);
            bool centerSide = (dist >= 0);
            for (int i=0; i<points.Count; i++)
            {
                v = new Vector2(points[i].X - a.X, points[i].Y - a.Y);
                dist = Vector2.Dot(new Vector2(-n.Y, n.X), v);
                bool pointSide = (dist >= 0);
                if (pointSide != centerSide) outsiders.Add(points[i]);
            }
            return outsiders;
        }

        /** Finds the minimum bounding area containing all points in <param name="points">points</param>,
         * where the face of each point faces <param name="center">center</param>. */
        private List<Vector3> facePointArea(List<Vector3> points, Vector3 center) {
            List<WaterEdge> edges = new List<WaterEdge>();
            for (int i = 0; i < points.Count; i++ )
            {
                edges.Add(new WaterEdge(points[i], points[(i+1)%points.Count], new List<Vector3>()));
            }
            for (int i = 0; i < edges.Count; i++)
            {
                if (!edgeFacesPoint(edges[i], center))
                {
                    //for the other winding order
                    //int prev = (i + edges.Count - 1) % edges.Count;
                    //edges[prev] = new WaterEdge(edges[prev].NodeA, edges[i].NodeB, new List<Vector3>());
                    //edges.RemoveAt(i);
                    //i = (i + edges.Count - 2) % edges.Count;
                    //i -= 2;
                    //if (i < 0) i = 0;

                    int next = (i + 1) % edges.Count;
                    edges[i] = new WaterEdge(edges[i].NodeA, edges[next].NodeB, new List<Vector3>());
                    edges.RemoveAt(next);
                    i--;
                }
            }
            List<Vector3> boundPoits = new List<Vector3>(edges.Count);
            for (int i = 0; i < edges.Count; i++) {
                boundPoits.Add(edges[i].NodeA);
            }
            return boundPoits;
        }

        private bool edgeFacesPoint(WaterEdge edge, Vector3 point) {
            Vector2 n = Vector2.Normalize(new Vector2(edge.NodeA.X - edge.NodeB.X, edge.NodeA.Y - edge.NodeB.Y));
            Vector2 v = new Vector2(point.X - edge.NodeA.X, point.Y - edge.NodeA.Y);
            float dist = Vector2.Dot(new Vector2(-n.Y, n.X), v);
            //if (dist <= 0) Console.WriteLine("No Face!");
            return (dist > 0);
        }

        private bool notEdgePoint(Vector3 p, LevelInfo levelInfo) 
        {
            return (p.X > 0 && p.X < levelInfo.getWidth()-1 && p.Y > 0 && p.Y < levelInfo.getHeight()-1);
        }

        private static bool[,] waterMap;
        private static int width, height;
        private static Vector4[,] map;

        public static List<List<Vector3>> findWater(LevelInfo levelInfo)
        {
            height = levelInfo.getHeight();
            width = levelInfo.getHeight();
            map = levelInfo.TextureMap;
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

        private static List<Vector3> depthFirstSearch(Vector3 start, Vector3 end)
        {
            List<Vector3> edgePoints = new List<Vector3>();
            depthFirstSearch(start, end, edgePoints);
            return edgePoints;
        }

        private static Vector3 depthFirstSearch(Vector3 curr, Vector3 goal, List<Vector3> path)
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

        private static bool isEdge(int x, int y)
        {
            if (map[x, y].X >= WATER_THRESHOLD)
            {
                if (y > 0) {
                    if (map[x, y-1].X < WATER_THRESHOLD) return true;

                    if (x > 0) {
                        if (map[x-1, y-1].X < WATER_THRESHOLD || map[x-1, y].X < WATER_THRESHOLD) return true;
                    }
                    else return true;

                    if (x < width-1) {
                        if (map[x+1, y-1].X < WATER_THRESHOLD || map[x+1, y].X < WATER_THRESHOLD) return true;
                    }
                    else return true;

                }
                else return true;

                if (y < height-1) {
                    if (map[x, y+1].X < WATER_THRESHOLD) return true;

                    if (x > 0) {
                        if (map[x-1, y+1].X < WATER_THRESHOLD) return true;
                    }
                    else return true;

                    if (x < width-1) {
                        if (map[x+1, y+1].X < WATER_THRESHOLD) return true;
                    }
                    else return true;
                }
                else return true;
            }
            return false;
        }
    }

    /** Represents a point on the bounding polygon of a body of water. */
    class WaterNode
    {
        private Vector3 point;
        public Vector3 Point { get { return point; } }

        private int index;
        public int Index { get { return index; } }

        public WaterNode(Vector3 aPoint, int anIndex)
        {
            point = aPoint;
            index = anIndex;
        }
    }

    /** Represents an edge on the bounding polygon of a body of water. */
    class WaterEdge
    {
        private Vector3 nodeA, nodeB;
        public Vector3 NodeA { get { return nodeA; } }
        public Vector3 NodeB { get { return nodeB; } }

        private bool closed;
        public bool Closed { get { return closed; } }

        private List<Vector3> outsiders;

        public WaterEdge(Vector3 a, Vector3 b, List<Vector3> o)
        {
            nodeA = a;
            nodeB = b;
            closed = (o.Count == 0);
            outsiders = o;
        }

        public bool isOutside(Vector3 aNode)
        {
            return outsiders.Contains(aNode);
        }
    }
}
