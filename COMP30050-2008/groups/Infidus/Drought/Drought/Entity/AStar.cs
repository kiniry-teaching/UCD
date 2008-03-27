using System;
using System.Collections.Generic;
using System.Text;
using Microsoft.Xna.Framework;

namespace Drought.Entity
{
    class AStar
    {
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

                if (n.Equals(goal)) //do data equals
                    ;//return solution

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
            nodes.Add(new Vector3(startX, startY));
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
                return nodes[x,y];
            return null;
        }
    }

    class Node
    {
        private Node parent;

        private float f;

        private float g;

        private float h;


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

        public Node getParent()
        {
            return parent;
        }

        public void setParent(Node parent)
        {
            this.parent = parent;
        }
    }
}
