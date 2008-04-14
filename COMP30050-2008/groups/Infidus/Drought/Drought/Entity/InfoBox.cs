using Microsoft.Xna.Framework.Graphics;
using Drought.State;
using Microsoft.Xna.Framework;
using Drought.Graphics;

namespace Drought.Entity
{
    /**
     * A floating box which displays above an Entity when it is highlighted.
     * Shows the unit's current health and water.
     */
    class InfoBox
    {
        private Texture2D bar;

        private VertexDeclaration vertexDeclaration;

        private Effect billboardEffect;

        private VertexPositionNormalTexture[] pointList;

        private short[] indices;

        public InfoBox(GameState state) {
            bar = state.getContentManager().Load<Texture2D>("Textures/infobox");
            
            vertexDeclaration = new VertexDeclaration(state.getGraphics(), VertexPositionNormalTexture.VertexElements);

            billboardEffect = state.getContentManager().Load<Effect>("EffectFiles/healthbox");

            pointList = new VertexPositionNormalTexture[4];
            pointList[0] = new VertexPositionNormalTexture(new Vector3(0, 0, 0), Vector3.Forward, new Vector2(1, 1));
            pointList[1] = new VertexPositionNormalTexture(new Vector3(0, 0, 6), Vector3.Forward, new Vector2(1, 0));
            pointList[2] = new VertexPositionNormalTexture(new Vector3(16, 0, 0), Vector3.Forward, new Vector2(0, 1));
            pointList[3] = new VertexPositionNormalTexture(new Vector3(16, 0, 6), Vector3.Forward, new Vector2(0, 0));

            indices = new short[6];
            indices[0] = 0;
            indices[1] = 1;
            indices[2] = 2;
            indices[3] = 1;
            indices[4] = 3;
            indices[5] = 2;
        }

        public void updatePosition(Vector3 newPosition)
        {
            pointList[0].Position.X = newPosition.X;
            pointList[0].Position.Y = newPosition.Y;
            pointList[0].Position.Z = newPosition.Z;

            pointList[1].Position.X = newPosition.X;
            pointList[1].Position.Y = newPosition.Y;
            pointList[1].Position.Z = newPosition.Z + 6;

            //pointList[2].Position.X = newPosition.X + 16;
            pointList[2].Position.X = newPosition.X;
            pointList[2].Position.Y = newPosition.Y;
            pointList[2].Position.Z = newPosition.Z;

            //pointList[3].Position.X = newPosition.X + 16;
            pointList[3].Position.X = newPosition.X;
            pointList[3].Position.Y = newPosition.Y;
            pointList[3].Position.Z = newPosition.Z + 6;
        }

        public void render(SpriteBatch batch)
        {
            batch.Begin();
            batch.Draw(bar, new Rectangle(50, 50, bar.Width, bar.Height), Color.White);
            batch.End();
        }

        public void render(GraphicsDevice graphics, Matrix view, Matrix projection)
        {
            graphics.VertexDeclaration = vertexDeclaration;

            billboardEffect.CurrentTechnique = billboardEffect.Techniques["Billboard"];
            billboardEffect.Parameters["World"].SetValue(Matrix.Identity);
            billboardEffect.Parameters["View"].SetValue(view);
            billboardEffect.Parameters["Projection"].SetValue(projection);
            billboardEffect.Parameters["xTexture"].SetValue(bar);

            billboardEffect.Begin();
            foreach (EffectPass pass in billboardEffect.CurrentTechnique.Passes) {
                pass.Begin();

                graphics.DrawUserIndexedPrimitives<VertexPositionNormalTexture>(PrimitiveType.TriangleList,
                    pointList,
                    0,
                    4,
                    indices,
                    0,
                    2);

                pass.End();
            }
            billboardEffect.End();
        }
    }
}
