using System;
using System.Collections.Generic;
using System.Text;
using Microsoft.Xna.Framework;

namespace Drought.Pathfinding
{
    /**
     * A Node used in the A* algorithm.
     */
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


        /**
         * Constructs a new node with the specified coordinates. All other
         * node values are initialised to 0.
         */
        public Node(int x, int y)
        {
            pos = new Vector2(x, y);
        }

        /**
         * Gets/sets the heuristic value to move from this node to the goal node.
         * The nodes's f value is automatically updated when this value is changed.
         */
        public float hVal
        {
            set { h = value; f = g + h; }
            get { return h; }
        }

        /**
         * Gets/sets the the cost to get to this node from the start node.
         * The nodes's f value is automatically updated when this value is changed.
         */
        public float gVal
        {
            set { g = value; f = g + h; }
            get { return g; }
        }

        /**
         * Gets the estimated cost to move from the start node to the goal 
         * node going through this node.
         * 
         * @return The node's f value.
         */
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
