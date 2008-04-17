using System;
using System.Collections.Generic;
using System.Text;
using Microsoft.Xna.Framework;
using Microsoft.Xna.Framework.Graphics;

namespace Drought.World
{

    /** Represents a point on the bounding polygon of a body of water. */
    class WaterNode
    {
        private Vector3 point;
        public Vector3 Point { get { return point; } }
        private int index;
        public int Index { get { return index; } }

        public WaterNode(Vector3 aPoint, int anIndex) {
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

        public WaterEdge(Vector3 a, Vector3 b, List<Vector3> o) {
            nodeA = a;
            nodeB = b;
            closed = (o.Count == 0);
            outsiders = o;
        }

        public bool isOutside(Vector3 aNode) {
            return outsiders.Contains(aNode);
        }
    }

    /** A continuous body of water. */
    class Water
    {
        private VertexPositionColor[] vertices;
        private VertexDeclaration vd;
        private BasicEffect effect;
        
        public Water(List<Vector3> points, HeightMap heightMap, GraphicsDevice graphics)
        {
            initialize(points, heightMap);
            vd = new VertexDeclaration(graphics, VertexPositionColor.VertexElements);
            effect = new BasicEffect(graphics, null);
        }

        public void initialize(List<Vector3> points, HeightMap heightMap)
        {
            Vector3 averageCenter = new Vector3(0, 0, 0);
            Vector3 boxCenter = new Vector3(0, 0, 0);
            float xMin = float.MaxValue; int xMinPos = -1; float xMax = float.MinValue; int xMaxPos = -1;
            float yMin = float.MaxValue; int yMinPos = -1; float yMax = float.MinValue; int yMaxPos = -1;
            for (int i = 0; i < points.Count; i++)
            {
                points[i] = new Vector3(points[i].X, points[i].Y, heightMap.getHeight(points[i].X, points[i].Y) + 0.01f);
                if (points[i].X < xMin) { xMin = points[i].X; xMinPos = i; }
                if (points[i].X > xMax) { xMax = points[i].X; xMaxPos = i; }
                if (points[i].Y < yMin) { yMin = points[i].Y; yMinPos = i; }
                if (points[i].Y > yMax) { yMax = points[i].Y; yMaxPos = i; }
                averageCenter += points[i];
            }
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
            for (int i = 0; i < finalPoints.Count; i++)
            {
                vertices[i+1].Position = new Vector3(finalPoints[i].X, finalPoints[i].Y, averageCenter.Z);
            }
            vertices[vertices.Length - 1] = vertices[1];
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
    }
}
