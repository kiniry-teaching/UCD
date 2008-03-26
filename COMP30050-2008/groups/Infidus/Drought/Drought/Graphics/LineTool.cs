using System.Collections.Generic;
using Microsoft.Xna.Framework;
using Microsoft.Xna.Framework.Graphics;
using System;

namespace Drought.Graphics {

    /**
     * A general purpose line drawing tool.
     * Can draw to world coordinates given View and Projection matrices, or directly to the screen.
     * Lines are drawn as a strip; each line segment starts where the previous one ended.
     * So to draw 3 lines, for example, 4 points are needed.
     */
    class LineTool 
    {
        /** The GraphicsDevice to draw to. */
        private GraphicsDevice graphics;

        private VertexDeclaration vertexDeclaration;

        private BasicEffect basicEffect;

        /** The number of points in the line. */
        private int numPoints;

        /** The list of points in the line. */
        private VertexPositionNormalTexture[] pointList;

        short[] indices;

        public LineTool(GraphicsDevice graphicsDevice)
        {
            graphics = graphicsDevice;
            vertexDeclaration = new VertexDeclaration(graphics, VertexPositionNormalTexture.VertexElements);

            basicEffect = new BasicEffect(graphics, null);
            basicEffect.DiffuseColor = new Vector3(1.0f, 1.0f, 1.0f);

            numPoints = 0;
        }

        public void setColor(Vector3 color)
        {
            basicEffect.DiffuseColor = color;
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

            indices = new short[points.Count];
            for (short i = 0; i < points.Count; i++) {
                indices[i] = i;
            }
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
                
                graphics.DrawUserIndexedPrimitives<VertexPositionNormalTexture>(PrimitiveType.LineStrip,
                    pointList,
                    0,
                    numPoints,
                    indices,
                    0,
                    numPoints - 1);
                
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
