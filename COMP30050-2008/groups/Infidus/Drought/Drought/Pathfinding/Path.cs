using System;
using System.Collections.Generic;
using System.Text;
using Microsoft.Xna.Framework;
using Drought.World;

namespace Drought.Entity
{
    class Path
    {
        /** The nodes that make up the path. */
        private List<Vector3> nodes;

        /** The distance each node is at on the path. */
        private List<float> nodeDist;

        /** The total length of the path. */
        private Vector3 normal;

        private LevelInfo levelInfo;

        /** The total length of the path. */
        private float length;

        /** The amount of distance along the path covered so far. */
        private float coveredDist;

        /** The current position along the path. */
        private Vector3 position;

        /** Index of the node the position is either at or just passed. */
        private int currNode;


        public Path(List<Vector3> nodes, LevelInfo level)
        {
            this.nodes = nodes;
            this.levelInfo = level;
            nodeDist = new List<float>();

            //can't have an empty list of nodes
            if (nodes.Count == 0)
            {
                nodes = new List<Vector3>();
                nodes.Add(new Vector3(0, 0, 0));
            }

            initialise();
        }

        private void initialise()
        {
            currNode = 0;
            position = nodes[0];
            normal = levelInfo.getNormal((int)position.X, (int)position.Y);
            length = 0.0f;

            for (int i = 0; i < nodes.Count - 1; i++)
            {
                nodeDist.Add(length);
                length += Vector3.Distance(nodes[i], nodes[i + 1]);
            }
            nodeDist.Add(length);
        }

        /**
         * Gets the total length of the path.
         * 
         * @return path's length.
         */
        public float getLength()
        {
            return length;
        }

        /**
         * Gets the current position along the path.
         * 
         * @return current position along the path.
         */
        public Vector3 getPosition()
        {
            return position;
        }

        /** 
         * Gets the normal at the current position along the path.
         * 
         * @return The normal at the current position.
         */
        public Vector3 getNormal()
        {
            return normal;
        }

        /**
         * Gets whether the entire path has been traversed.
         * 
         * @return True if entire path has been covered.
         */
        public bool isFinished()
        {
            return coveredDist == length;
        }

        /**
         * Adds a specified distance to the amount of the path
         * that has been covered and computes the new position
         * along the path. distance >= 0.
         * 
         * @param distance The distance to add on. distance >= 0
         */
        public void addDistance(float distance)
        {
            coveredDist += distance;
            if (coveredDist >= length) //we're finished
            {
                coveredDist = length;
                currNode = nodes.Count - 1;
                position = nodes[currNode];
                return;
            }

            while (coveredDist > nodeDist[currNode + 1])
                currNode++;

            Vector3 curr = nodes[currNode];
            Vector3 next = nodes[currNode + 1];
            float amt = (coveredDist - nodeDist[currNode]) / Vector3.Distance(curr, next);
            position = Vector3.Lerp(curr, next, amt);
            //Vector3 currNorm = normalMap.getNormal((int)curr.X, (int)curr.Y);
            //Vector3 nextNorm = normalMap.getNormal((int)next.X, (int)next.Y);
            //normal = Vector3.Lerp(currNorm, nextNorm, amt);
            normal = levelInfo.getNormal(position.X, position.Y);
        }

        /**
         * Gets the index of the next node in the path. This is
         * usually currNode + 1 but when the curr
         *
        private int getNextNodeIndex()
        {
            if (currNode + 1 >= nodes.Count)
                return currNode;
            return currNode + 1;
        }
        */

        /**
         * Gets a list containing the current position and all
         * positions that have not yet been passed.
         * 
         * @return List containing the current and remaining positions in the path.
         */
        public List<Vector3> getRemainingPath()
        {
            List<Vector3> remainingPath = new List<Vector3>();
            remainingPath.Add(position);

            for (int i = currNode + 1; i < nodes.Count; i++) {
                remainingPath.Add(nodes[i]);
            }
            return remainingPath;
        }
    }
}
