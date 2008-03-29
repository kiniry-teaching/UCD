using System;
using System.Collections.Generic;
using System.Text;
using Microsoft.Xna.Framework;
using Drought.World;

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

        private LevelInfo level;

        /** Map to lookup whether a specific node is traversable. True indicates a traversable node. */
        private bool[,] traversable;

        /** Width of the map. */
        private int width;

        /** Height of the map. */
        private int height;


        public AStar(LevelInfo level)
        {
            initialise(level);
        }

        public void initialise(LevelInfo level)
        {
            this.level = level;
            width = level.getWidth();
            height = level.getHeight();
            traversable = new bool[width, height];

            //create nodes
            for (int x = 0; x < width; x++)
                for (int y = 0; y < height; y++)
                {
                    //TODO initialise traversable map to appropriate values
                }
        }

        public Path computePath(float startX, float startY, float endX, float endY)
        {
            List<Node> open = new List<Node>();
            List<Node> closed = new List<Node>();
            Node goal = getNode((int)endX, (int)endY);
            Node start = getNode((int)startX, (int)startY);

            if(goal != null && start != null)
                open.Add(start);
            //else a path can't be found so skip to the end and return default path.

            while (open.Count > 0)
            {
                //get node with lowest f value from open list (last entry in list)
                Node n = open[open.Count - 1];
                open.RemoveAt(open.Count - 1);
                closed.Add(n);

                if (n.getPosition() == goal.getPosition()) //found a path
                {
                    Node curr = n;
                    Node parent = n.getParent();
                    List<Vector3> pathNodes = new List<Vector3>();
                    Vector2 pos = n.getPosition();
                    
                    pathNodes.Add(new Vector3(pos.X, pos.Y, level.getHeight(pos.X, pos.Y)));

                    while (parent != null)
                    {
                        pos = parent.getPosition();
                        pathNodes.Add(new Vector3(pos.X, pos.Y, level.getHeight(pos.X, pos.Y)));
                    }
                    
                    return new Path(pathNodes, level);
                }

                //generate successors for n
                List<Node> successors = getSuccessors(n);

                for (int i = 0, m = successors.Count; i < m; i++)
                {
                    Node s = successors[i];

                    //s.h is estimated distance to goal
                    s.hVal = Vector2.Distance(s.getPosition(), goal.getPosition());
                    //s.g is n.g + cost from n to s
                    s.gVal = n.gVal + s.getDistanceToParent();


                    //If it isn’t on the open list, add it to the open list.
                    Node oldNode = contains(open, s);
                    if (oldNode != null)
                        orderedAdd(open, s);
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
                            //TODO reorder open list
                        }
                    }

                }
            }


            //couldn't find a path so return a path containing just the start node
            List<Vector3> nodes = new List<Vector3>();
            nodes.Add(new Vector3(startX, startY, level.getHeight(startX, startY)));
            return new Path(nodes, level);
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
            if(x >= 0 && x < width && y >= 0 && y < height)
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
            if(x >= 0 && x < width && y >= 0 && y < height)
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

            for(int i = 0; i < BORDER_NODES.Length; i++)
            {
                Vector2 pos = node.getPosition() + BORDER_NODES[i];
                Node n = getNode((int)pos.X, (int)pos.Y);

                if (n != null && canMove(node, n))
                {
                    Node s = new Node((int)pos.X, (int)pos.Y);
                    s.setParent(n);
                    successors.Add(s);
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
            //TODO
            return false;
        }

        /**
         * Checks if a node is contained in a list. Equality is determined
         * by the node's position.
         * 
         * @param list The list to check in.
         * @param node The node to check for.
         * @return The node if found of null if not found.
         */
        private Node contains(List<Node> list, Node node)
        {
            for (int i = 0, n = list.Count; i < n; i++)
                if (list[i].getPosition() == node.getPosition())
                    return list[i];
            return null;
        }

        private void orderedAdd(List<Node> list, Node node)
        {
            //TODO
            //keep open list sorted by f value ranging from lowest to highest
        }
    }


    class Node
    {
        /** Node's parent or null if no parent exists. */
        private Node parent;

        /** Node's position. */
        private Vector2 pos;

        /** The estimated cost to move from the start node to the goal node going through this node. */
        private float f;

        /** The cost to get to this node from the start node. */
        private float g;

        /** Heuristic value to move from this node to the goal node. */
        private float h;

        /** The distance to the node's parent or 0 if no parent exists. */
        private float distToParent;


        public Node()
        {
            pos = new Vector2();
        }

        public Node(int x, int y)
        {
            pos = new Vector2(x, y);
        }

        public float hVal
        {
            set { h = value; f = g + h;  }
            get { return h; }
        }

        public float gVal
        {
            set { g = value; f = g + h; }
            get { return g; }
        }

        public float getFVal()
        {
            return f;
        }

        /**
         * Gets the distance from this node to its parent
         * node. If no parent exists then 0.0f is returned.
         * 
         * @return The distance to the parent node.
         */
        public float getDistanceToParent()
        {
            return distToParent;
        }

        /**
         * Gets the node's parent. Returns null if no
         * parent node exists.
         * 
         * @return Node's parent.
         */
        public Node getParent()
        {
            return parent;
        }

        /**
         * Sets the parent of this node and calculates the
         * distance to it. If a null parameter is provided
         * then this node has no parent.
         * 
         * @param parent The parent node to set or null if the node is to have no parent.
         */
        public void setParent(Node parent)
        {
            this.parent = parent;

            if (parent != null)
                distToParent = Vector2.Distance(pos, parent.pos);
            else
                distToParent = 0.0f;
        }

        /**
         * Gets the node's position.
         * 
         * @return node's position.
         */
        public Vector2 getPosition()
        {
            return pos;
        }
    }
}
