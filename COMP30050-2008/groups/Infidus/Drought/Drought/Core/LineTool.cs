using System.Collections.Generic;
using Microsoft.Xna.Framework;
using Microsoft.Xna.Framework.Graphics;

namespace Drought.Core {

    /**
     * A general purpose line drawing tool.
     * Can draw to world coordinates give View and Projection matrices, or directly to the screen.
     * Lines are drawn as a strip; each line segment starts where the previous one ended.
     * So to draw 3 lines, for example, 4 points are needed.
     */
    class LineTool 
    {
        /** The GraphicsDevice to draw to. */
        private GraphicsDevice graphics;

        VertexDeclaration vertexDeclaration;

        BasicEffect basicEffect;

        /** The number of points in the line. */
        int numPoints;

        /** The list of points in the line. */
        VertexPositionNormalTexture[] pointList;

        VertexBuffer vertexBuffer;

        IndexBuffer indexBuffer;

        public LineTool(GraphicsDevice graphicsDevice)
        {
            graphics = graphicsDevice;
            vertexDeclaration = new VertexDeclaration(graphics, VertexPositionNormalTexture.VertexElements);

            basicEffect = new BasicEffect(graphics, null);
            basicEffect.DiffuseColor = new Vector3(1.0f, 1.0f, 1.0f);
        }

        /** Specify a new list of points to be used to draw the line. */
        public void setPointsList(List<Vector3> points)
        {
            pointList = new VertexPositionNormalTexture[points.Count];
            numPoints = points.Count;

            int x = 0;
            foreach (Vector3 point in points) {
                pointList[x++] = new VertexPositionNormalTexture(point, Vector3.Forward, new Vector2());
            }

            vertexBuffer = new VertexBuffer(graphics, 
                VertexPositionNormalTexture.SizeInBytes * (pointList.Length), BufferUsage.None);
            vertexBuffer.SetData<VertexPositionNormalTexture>(pointList);

            short[] indices = new short[points.Count];
            for (short i = 0; i < points.Count; i++) {
                indices[i] = i;
            }

            indexBuffer = new IndexBuffer(graphics,
                sizeof(short) * indices.Length, BufferUsage.None, IndexElementSize.SixteenBits);
            indexBuffer.SetData<short>(indices);
        }

        /** Draw the lines, using the specified transformational matrices. */
        public void render(Matrix view, Matrix projection)
        {
            // if there's less than 2 points, we're not going to draw any lines
            if (numPoints < 2) return;

            graphics.VertexDeclaration = vertexDeclaration; 
            
            basicEffect.View = view;
            basicEffect.Projection = projection;

            basicEffect.Begin();
            foreach (EffectPass pass in basicEffect.CurrentTechnique.Passes) {
                pass.Begin();

                graphics.Vertices[0].SetSource(vertexBuffer, 0, VertexPositionNormalTexture.SizeInBytes);

                graphics.Indices = indexBuffer;

                graphics.DrawIndexedPrimitives(
                    PrimitiveType.LineStrip,
                    0, // vertex buffer offset to add to each element of the index buffer
                    0, // minimum vertex index
                    numPoints, // number of vertices
                    0, // first index element to read
                    numPoints-1);// number of primitives to draw

                pass.End();
            }
            basicEffect.End();
        }

        /** Draw the lines directly to the screen surface. */
        public void render() {
            render(Matrix.Identity, Matrix.Identity);
        }
    }
}
