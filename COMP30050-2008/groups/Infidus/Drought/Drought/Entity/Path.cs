using System;
using System.Collections.Generic;
using System.Text;
using Microsoft.Xna.Framework;

namespace Drought.Entity
{
    class Path
    {
        /** The nodes that make up the path */
        private List<Vector3> nodes;

        /** The distance each node is at on the path */
        private List<float> nodeDist;

        private Vector3 position;

        private float length;

        private float coveredDist;

        private int currNode;

        public Path(List<Vector3> nodes)
        {
            this.nodes = nodes;
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
            length = 0.0f;

            for (int i = 0; i < nodes.Count - 1; i++)
            {
                nodeDist.Add(length);
                length += Vector3.Distance(nodes[i], nodes[i + 1]);
            }
            nodeDist.Add(length);
        }

        public float getLength()
        {
            return length;
        }

        public Vector3 getPosition()
        {
            return position;
        }

        public bool isFinished()
        {
            return coveredDist == length;
        }

        public void addDistance(float distance)
        {
            coveredDist += distance;
            if (coveredDist >= length) //we're finished
            {
                coveredDist = length;
                position = nodes[nodes.Count - 1];
                return;
            }

            while (coveredDist > nodeDist[getNextNodeIndex()])
                currNode++;

            Vector3 curr = nodes[currNode];
            Vector3 next = nodes[currNode + 1];
            float amt = (coveredDist - nodeDist[currNode]) / Vector3.Distance(curr, next);
            position = Vector3.Lerp(curr, next, amt);
        }

        private int getNextNodeIndex()
        {
            if (currNode + 1 >= nodes.Count)
                return currNode;
            return currNode + 1;
        }
    }
}
