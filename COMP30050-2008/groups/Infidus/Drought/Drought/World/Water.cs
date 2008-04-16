using System;
using System.Collections.Generic;
using System.Text;
using Microsoft.Xna.Framework;
using Microsoft.Xna.Framework.Graphics;

namespace Drought.World
{
    class Water
    {
        Vector3[] points;
        VertexPositionColor[] vertices;
        VertexDeclaration vd;
        BasicEffect effect;

        HeightMap heightMap;

        
        public Water(Vector3[] points, HeightMap heightMap)
        {
            this.points = points;
            this.heightMap = heightMap;

            vertices = new VertexPositionColor[points.Length+2];
            initialize();
        }

        public void initialize()
        {
            Vector3 center = new Vector3(0, 0, 0);

            for (int i = 0; i < points.Length; i++)
            {
                points[i].Z = heightMap.getHeight(points[i].X, points[i].Y) + 0.01f;
                center += points[i];
            }
            center /= points.Length;

            smoothArray(points);

            vertices[0].Position = center;
            for (int i = 0; i < points.Length; i++)
            {
                points[i].Z = center.Z;
                vertices[i+1].Position = points[i];
            }
            vertices[vertices.Length - 1] = vertices[1];
        }

        private void smoothArray(Vector3[] array)
        {
            for (int i = 0; i < array.Length; i++)
            {
                points[(i + 1) % array.Length] = (points[i] + points[(i + 2) % array.Length])/2;
            }
        }

        public void render(GraphicsDevice graphics, Matrix viewMatrix, Matrix projectionMatrix)
        {
            if (vd == null)
            {
                vd = new VertexDeclaration(graphics, VertexPositionColor.VertexElements);
            }
            graphics.VertexDeclaration = vd;


            if (effect == null)
            {
                effect = new BasicEffect(graphics, null);
            }

            if (points.Length > 1)
            {
                graphics.RenderState.AlphaBlendEnable = true;
                graphics.RenderState.SourceBlend = Blend.SourceAlpha;
                graphics.RenderState.DestinationBlend = Blend.InverseSourceAlpha;

                effect.DiffuseColor = Color.LightBlue.ToVector3();
                effect.Alpha = 0.5f;
                effect.World = Matrix.Identity;
                effect.View = viewMatrix;
                effect.Projection = projectionMatrix;

                effect.Begin();
                foreach (EffectPass pass in effect.CurrentTechnique.Passes)
                {
                    pass.Begin();

                    graphics.DrawUserPrimitives<VertexPositionColor>(PrimitiveType.TriangleFan, vertices, 0, vertices.Length - 2);

                    pass.End();
                }
                effect.End();
            }
        }
    }
}
