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

        private Vector3 normal;

        private NormalMap normalMap;

        private float length;

        private float coveredDist;

        private int currNode;

        public Path(List<Vector3> nodes, NormalMap normalMap)
        {
            this.nodes = nodes;
            this.normalMap = normalMap;
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
            normal = normalMap.getNormal((int)position.X, (int)position.Y);
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

        public Vector3 getNormal()
        {
            return normal;
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
            //Vector3 currNorm = normalMap.getNormal((int)curr.X, (int)curr.Y);
            //Vector3 nextNorm = normalMap.getNormal((int)next.X, (int)next.Y);
            //normal = Vector3.Lerp(currNorm, nextNorm, amt);
            normal = normalMap.getNormal(position.X, position.Y);
        }

        private int getNextNodeIndex()
        {
            if (currNode + 1 >= nodes.Count)
                return currNode;
            return currNode + 1;
        }
    }
}
