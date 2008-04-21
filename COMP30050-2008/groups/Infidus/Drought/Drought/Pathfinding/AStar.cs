using System;
using System.Collections.Generic;
using System.Text;
using Microsoft.Xna.Framework;
using Drought.Pathfinding;
using Drought.World;
using System.Diagnostics;

namespace Drought.Entity
{
    class AStar
    {
        /** Offsets of the nodes surrounding a node */
        private static Vector2[] BORDER_NODES = new Vector2[] { 
            new Vector2(-1, -1), //bottom left
            new Vector2(0, -1), //bottom centre
            new Vector2(1, -1), //bottom right
            new Vector2(-1, 0), //left
            new Vector2(1, 0), //right
            new Vector2(-1, 1), //top left
            new Vector2(0, 1), //top center
            new Vector2(1, 1), }; //top right

        /** Can move from one node to another if the other node is not greater than MAX_MOVE_DIST. */
        private const float MAX_MOVE_DIST = 2.5f;

        private const int SCALE = 5;

        /** The level information to search for paths. */
        private LevelInfo level;

        /** A scaled down of LevelInfo's heightmap for A* to search. */
        private float[,] scaledHeightMap;

        /** Map to lookup whether a specific node is traversable. True indicates a traversable node. */
        private bool[,] traversable;

        /** Width of the map. */
        private int width;

        /** Height of the map. */
        private int height;


        private Stopwatch timer = new Stopwatch();


        /**
         * Constructs and initialises AStar to search for paths in the
         * current level info.
         * 
         * @param level The level information to search.
         */
        public AStar(LevelInfo level)
        {
            initialise(level);
        }

        /**
         * Initialises AStar to search for paths in a level.
         * This method must be called whenever levelInfo changes
         * to keep AStar up to date with the latest level.
         * 
         * @param level The level information to search.
         */
        public void initialise(LevelInfo level)
        {
            this.level = level;
            width = level.getWidth() / SCALE;
            height = level.getHeight() / SCALE;
            scaledHeightMap = new float[width, height];
            traversable = new bool[width, height];

            for (int x = 0; x < width; x++)
                for (int y = 0; y < height; y++)
                {
                    scaledHeightMap[x, y] = level.getHeight(x * SCALE, y * SCALE);

                    //if a water texture then a node is not traversable
                    traversable[x, y] = level.getTextureValue(x * SCALE, y * SCALE).X > 0 ? false : true;
                }

            //set the border of the map to be non-traversable
            for (int x = 0; x < width; x++)
            {
                traversable[x, 0] = false;
                traversable[x, height - 1] = false;
            }

            for (int y = 0; y < height; y++)
            {
                traversable[0, y] = false;
                traversable[width - 1, y] = false;
            }

            /*
            StringBuilder sb = new StringBuilder();
            for (int x = 0; x < width; x++)
            {
                sb.Append("\n");
                for (int y = 0; y < height; y++)
                    sb.Append(level.getHeight(x, y) + " ");
            }
            Console.WriteLine(sb);
             */
        }

        public Path computePath(float startX, float startY, float endX, float endY, out bool pathFound)
        {
            timer.Reset();
            timer.Start();

            Heap open = new Heap();
            //List<Node> closed = new List<Node>();
            bool[,] closed = new bool[width, height];
            int closedSize = 0;
            Node[,] openMap = new Node[width, height];
            Node goal = getNode((int) Math.Round(endX / SCALE), (int) Math.Round(endY / SCALE));
            Node start = getNode((int) Math.Round(startX / SCALE), (int) Math.Round(startY / SCALE));

            if (goal != null && start != null)
            {
                open.insert(start);
                openMap[(int)start.getPosition().X, (int)start.getPosition().Y] = start;
            }
            //else a path can't be found so skip to the end and return default path.

            while (!open.isEmpty())
            {
                //get node with lowest f value from open list (last entry in list)
                Node n = open.removeMin();
                openMap[(int)n.getPosition().X, (int)n.getPosition().Y] = null;

                //closed.Add(n);
                closed[(int)n.getPosition().X, (int)n.getPosition().Y] = true;
                closedSize++;

                if (n.getPosition() == goal.getPosition()) //found a path
                {
                    Node parent = n.getParent();
                    List<Vector3> pathNodes = new List<Vector3>();
                    Vector2 pos = n.getPosition();

                    pathNodes.Add(new Vector3(pos.X * SCALE, pos.Y * SCALE, scaledHeightMap[(int)pos.X, (int)pos.Y]));

                    while (parent != null)
                    {
                        pos = parent.getPosition();
                        pathNodes.Add(new Vector3(pos.X * SCALE, pos.Y * SCALE, scaledHeightMap[(int)pos.X, (int)pos.Y]));
                        parent = parent.getParent();
                    }

                    pathNodes.Add(level.getPositionAt(startX, startY));

                    Console.WriteLine("closed size: " + closedSize);
                    Console.WriteLine(timer.ElapsedMilliseconds + "ms total to run A*");
                    timer.Stop();

                    pathNodes.Reverse();
                    pathNodes.Add(level.getPositionAt(endX, endY));
                    pathFound = true;
                    return new Path(pathNodes);
                }

                //generate successors for n
                List<Node> successors = getSuccessors(n);

                for (int i = 0, m = successors.Count; i < m; i++)
                {
                    Node s = successors[i];

                    //if (!contains(closed, s))
                    if(closed[(int)s.getPosition().X, (int)s.getPosition().Y] == false)
                    {
                        //s.h is estimated distance to goal
                        //s.hVal = Vector2.Distance(s.getPosition(), goal.getPosition());
                        s.hVal = Vector2.DistanceSquared(s.getPosition(), goal.getPosition());
                        //s.g is n.g + cost from n to s
                        s.gVal = n.gVal + s.getDistanceToParent();


                        //If it isn’t on the open list, add it to the open list.
                        //Node oldNode = open.contains(s.getPosition(), out oldNodePos);
                        int sx = (int)s.getPosition().X;
                        int sy = (int)s.getPosition().Y;
                        Node oldNode = openMap[sx, sy];

                        if (oldNode == null)
                        {
                            open.insert(s);
                            openMap[sx, sy] = s;
                        }
                        else
                        {
                            //If it is on the open list already, check to see if this path to that square is better,
                            //using G cost as the measure. A lower G cost means that this is a better path.
                            //If so, change the parent of the square to the current square, and recalculate the G and F scores of the square.
                            //If you are keeping your open list sorted by F score, you may need to resort the list to account for the change.
                            if (s.gVal < oldNode.gVal)
                            {
                                oldNode.setParent(n);
                                oldNode.gVal = s.gVal;
                                open.reorderNode(oldNode.positionInHeap);
                            }
                        }
                    }
                }
            }

            Console.WriteLine("closed size: " + closedSize);
            Console.WriteLine("Took " + timer.ElapsedMilliseconds + "ms to not find a path");
            timer.Stop();

            //couldn't find a path so return a path containing just the start node
            List<Vector3> noPath = new List<Vector3>();
            noPath.Add(level.getPositionAt(startX, startY));
            pathFound = false;
            return new Path(noPath);
        }

        /**
         * Sets whether a point in the map is traversable.
         * 
         * @param x The x coordinate of the point.
         * @param y The y coordinate of the point.
         * @param value True for the point to be traversable, false otherwise.
         */
        public void setTraversable(int x, int y, bool value)
        {
            if (x >= 0 && x < width && y >= 0 && y < height)
                traversable[x, y] = value;
        }

        /**
         * Gets the node at the specified location. If the location is
         * invalid or the location is not traversable then null is returned.
         * 
         * @param x The x coordinate of the location.
         * @param y The y coordinate of the location.
         * @return Node The node at the location or null.
         */
        private Node getNode(int x, int y)
        {
            if (x >= 0 && x < width && y >= 0 && y < height)
                return traversable[x, y] ? new Node(x, y) : null;
            return null;
        }

        /**
         * Gets a list of successor nodes for a specified node.
         * Each successor node's parent is set to the speified node.
         * 
         * @param node The node to get successors for.
         */
        private List<Node> getSuccessors(Node node)
        {
            List<Node> successors = new List<Node>();

            for (int i = 0; i < BORDER_NODES.Length; i++)
            {
                Vector2 pos = node.getPosition() + BORDER_NODES[i];
                Node n = getNode((int)pos.X, (int)pos.Y);

                if (n != null && canMove(node, n))
                {
                    n.setParent(node);
                    successors.Add(n);
                }
            }

            return successors;
        }

        /**
         * Determines if it is possible to move between two adjacent nodes.
         * 
         * @param a The first node.
         * @param b The second node.
         * @return True if it is possible to move from a to b.
         */
        private bool canMove(Node a, Node b)
        {
            Vector2 posA = a.getPosition();
            Vector2 posB = b.getPosition();

            float diff = Math.Abs(scaledHeightMap[(int)posA.X, (int)posA.Y] - scaledHeightMap[(int)posB.X, (int)posB.Y]);

            return diff <= MAX_MOVE_DIST;
        }

    }
}
