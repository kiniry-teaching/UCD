using System;
using System.Collections.Generic;
using System.Text;

namespace Drought.Pathfinding
{
    class Heap
    {
        /** The default initial size of the heap's internal data array. */
        private static int DEFAULT_SIZE = 50;

        /** The heap's internal data array. */
        private Node[] nodes;

        /** The number of elements in the heap. */
        private int size;


        public Heap()
        {
            nodes = new Node[DEFAULT_SIZE];
        }

        public void insert(Node node)
        {
            if (size == nodes.Length)
                growArray();

            nodes[size] = node;
            size++;

            //parent of element i is floor of (i - 1)/2
            int currNodeIndex = size;
            bool done = false;
            while(!done)
            {
                int parentIndex = (currNodeIndex - 1) / 2;
                
                if (currNodeIndex == parentIndex)
                    done = true;
                else if (nodes[parentIndex].getFVal() < nodes[currNodeIndex].getFVal())
                {
                    swap(parentIndex, currNodeIndex);
                    currNodeIndex = parentIndex;
                }
                else
                    done = true;
            }
        }

        public Node removeMin()
        {
            if (size == 0)
                return null;

            Node min = nodes[0];
            nodes[0] = nodes[size - 1];
            size--;

            //children of element i are (2 * i) + 1 and (2 * i) + 2
            int currNodeIndex = size;
            bool done = false;
            while (!done)
            {
                int child1 = (currNodeIndex * 2) + 1;
                int child2 = (currNodeIndex * 2) + 2;

                if (child1 < size && child2 < size)
                {
                    int minChild = nodes[child1].getFVal() < nodes[child2].getFVal() ? child1 : child2;
                    if (nodes[currNodeIndex].getFVal() < nodes[minChild].getFVal())
                    {
                        swap(currNodeIndex, minChild);
                        currNodeIndex = minChild;
                    }
                    else
                        done = true;
                }
                else if (child1 < size)
                {
                    if (nodes[currNodeIndex].getFVal() < nodes[child1].getFVal())
                    {
                        swap(currNodeIndex, child1);
                        currNodeIndex = child1;
                    }
                    else
                        done = true;
                }
                else if (child2 < size)
                {
                    if (nodes[currNodeIndex].getFVal() < nodes[child2].getFVal())
                    {
                        swap(currNodeIndex, child2);
                        currNodeIndex = child2;
                    }
                    else
                        done = true;
                }
                else
                    done = true;
            }

            return min;
        }

        /**
         * Gets the number of elements in the heap.
         * 
         * @return number of elements in the heap.
         */
        public int getSize()
        {
            return size;
        }

        /**
         * Gets whether the heap has no elements in it.
         * 
         * @return True if the heap is empty.
         */
        public bool isEmpty()
        {
            return size == 0;
        }

        /**
         * Swaps two elements in the heap's array.
         * It is assumed that index a and b are both in range.
         * 
         * @param a Index of the first element to be swapped.
         * @param b Index of the second element to be swapped.
         */
        private void swap(int a, int b)
        {
            Node temp = nodes[a];
            nodes[a] = nodes[b];
            nodes[b] = temp;
        }

        /**
         * Grows the internal data array by doubling its size.
         */
        private void growArray()
        {
            Node[] old = nodes;
            nodes = new Node[old.Length * 2];
            Array.Copy(old, 0, nodes, 0, size);
        }
    }
}
