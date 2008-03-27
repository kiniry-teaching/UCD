using System;
using System.Collections.Generic;
using System.Text;
using Microsoft.Xna.Framework;

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

        private NormalMap normalMap;

        private Node[,] nodeMap;

        private int width;

        private int height;

        public AStar(NormalMap normalMap)
        {

        }

        public void initialise(NormalMap normalMap)
        {
            width = 0; //TODO map width
            height = 0; //TODO map height
            nodeMap = new Node[width, height];

            //create nodes
            for (int x = 0; x < width; x++)
                for (int y = 0; y < height; y++)
                {
                    //if traversable add node
                }
        }

        public Path computePath(float startX, float startY, float endX, float endY)
        {
            List<Node> open = new List<Node>();
            List<Node> closed = new List<Node>();
            Node goal = new Node();
            Node start = new Node();
            open.Add(start);

            while (open.Count > 0)
            {
                //get node with lowest f value from open list
                Node n = open[0];
                closed.Add(n);

                if (n.Equals(goal)) //TODO do data equals //found a path
                {
                    Node curr = n;
                    Node parent = n.getParent();
                    List<Vector3> pathNodes = new List<Vector3>();
                    Vector2 pos = n.getPosition();
                    pathNodes.Add(new Vector3(pos.X, pos.Y, heightMap.getHeight(pos.X, pos.Y)));

                    while (parent != null)
                    {
                        pos = parent.getPosition();
                        pathNodes.Add(new Vector3(pos.X, pos.Y, heightMap.getHeight(pos.X, pos.Y)));
                    }
                    
                    return new Path(pathNodes, normalMap);
                }

                //generate successors for n
                List<Node> successors = new List<Node>();

                for (int i = 0, m = successors.Count; i < m; i++)
                {
                    Node s = successors[i];
                    s.setParent(n);
                    //s.h is estimate distance to goal
                    //s.g is n.g + cost from n to s
                    //s.f is g.s + s.h

                    //if s is on the OPEN list and the existing one is as good or better then discard s and continue
                    //if s is on the CLOSED list and the existing one is as good or better then discard s and continue
                    //Remove occurrences of s from OPEN and CLOSED
                    //Add s to the OPEN list

                }
            }


            //couldn't find a path so return a path containing just the start node
            List<Vector3> nodes = new List<Vector3>();
            nodes.Add(new Vector3(startX, startY, heightMap.getHeight(startX, startY)));
            return new Path(nodes, normalMap);
        }

        /**
         * Gets the node at the specified location. If the location is
         * invalid then null is returned.
         * 
         * @param x The x coordinate of the location.
         * @param y The y coordinate of the location.
         * @return Node The node at the location or null.
         */
        private Node getNode(int x, int y)
        {
            if(x >= 0 && x < width && y >= 0 && y < height)
                return nodeMap[x,y];
            return null;
        }

        /**
         * Gets a list of successor nodes for a specified node.
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

                if (n != null)
                {
                    Node s = new Node((int)pos.X, (int)pos.Y);
                    s.setParent(n);
                    s.distanceToParent = Vector2.Distance(n.getPosition(), s.getPosition());

                    //add node to the list and compute its new values
                }
            }

            return successors;
        }
    }

    class Node
    {
        private Node parent;

        private Vector2 pos;

        private float f;

        private float g;

        private float h;

        private float distToParent;


        public Node()
        {
            pos = new Vector2();
        }

        public Node(int x, int y)
        {
            pos = new Vector2(x, y);
        }

        public float heuristic
        {
            set { h = value; }
            get { return h; }
        }

        public float cost
        {
            set { g = value; }
            get { return g; }
        }

        public float heuristicCost
        {
            set { f = value; }
            get { return f; }
        }

        public float distanceToParent
        {
            set { distToParent = value; }
            get { return distToParent; }
        }

        public Node getParent()
        {
            return parent;
        }

        public void setParent(Node parent)
        {
            this.parent = parent;
        }

        public Vector2 getPosition()
        {
            return pos;
        }
    }
}
