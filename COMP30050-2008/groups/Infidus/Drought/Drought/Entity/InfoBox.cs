using Microsoft.Xna.Framework.Graphics;
using Drought.State;
using Microsoft.Xna.Framework;
using Drought.Graphics;

namespace Drought.Entity
{
    /** The parameters InfoBox needs to pass to the graphics card to be rendered. */
    public struct InfoBoxVertex
    {
        public Vector3 Position;
        public Vector3 Offset;
        public Vector2 TexCoord;

        public InfoBoxVertex(Vector3 aPosition, Vector3 anOffset, Vector2 aTexCoord)
        {
            Position = aPosition;
            Offset = anOffset;
            TexCoord = aTexCoord;
        }

        public static int SizeInBytes = sizeof(float) * 8;
        public static VertexElement[] VertexElements = new VertexElement[]
        {
            new VertexElement( 0, 0, VertexElementFormat.Vector3, VertexElementMethod.Default, VertexElementUsage.Position, 0 ),
            new VertexElement( 0, sizeof(float) * 3, VertexElementFormat.Vector3, VertexElementMethod.Default, VertexElementUsage.Position, 1 ),
            new VertexElement( 0, sizeof(float) * 6, VertexElementFormat.Vector2, VertexElementMethod.Default, VertexElementUsage.TextureCoordinate, 0 ),
        };
    }

    /**
     * A floating box which displays above an Entity when it is highlighted.
     * Shows the unit's current health and water.
     */
    class InfoBox
    {
        /** The box unit info is displayed on. */
        private Texture2D box;

        private Texture2D heartEmpty, heartFull;
        private Texture2D waterEmpty, waterFull;

        private int fullHearts, totalHearts;
        private int fullWater, totalWater;

        private Vector4 position;

        /** How solid to draw this box. */
        private float opacity;

        /** The custom effect used to draw the billboard. */
        private Effect billboardEffect;

        private VertexDeclaration vertexDeclaration;
        private InfoBoxVertex[] pointList;
        //private VertexPositionTexture[] pointList;
        private short[] indices;

        public InfoBox(GameState state)
        {
            fullHearts = 5;
            totalHearts = 5;

            fullWater = 5;
            totalWater = 5;

            box = state.getContentManager().Load<Texture2D>("Textures/infobox");
            heartEmpty = state.getContentManager().Load<Texture2D>("Textures/heart-empty");
            heartFull = state.getContentManager().Load<Texture2D>("Textures/heart-full");
            waterEmpty = state.getContentManager().Load<Texture2D>("Textures/water-empty");
            waterFull = state.getContentManager().Load<Texture2D>("Textures/water-full");

            billboardEffect = state.getContentManager().Load<Effect>("EffectFiles/infobox");

            vertexDeclaration = new VertexDeclaration(state.getGraphics(), InfoBoxVertex.VertexElements);

            pointList = new InfoBoxVertex[4];

            pointList[0] = new InfoBoxVertex(new Vector3(), new Vector3(), new Vector2(1, 1));
            pointList[1] = new InfoBoxVertex(new Vector3(), new Vector3(), new Vector2(1, 0));
            pointList[2] = new InfoBoxVertex(new Vector3(), new Vector3(), new Vector2(0, 1));
            pointList[3] = new InfoBoxVertex(new Vector3(), new Vector3(), new Vector2(0, 0));

            indices = new short[6];
            indices[0] = 0;
            indices[1] = 1;
            indices[2] = 2;
            indices[3] = 1;
            indices[4] = 3;
            indices[5] = 2;
        }

        /** Should be called whenever the unit is moved to update the box's position. */
        public void update(Vector3 newPosition, float newOpacity, int currHealth, int maxHealth, int currWater, int maxWater)
        {
            fullHearts = currHealth;
            totalHearts = maxHealth;
            fullWater = currWater;
            totalWater = maxWater;
            position = new Vector4(newPosition.X, newPosition.Y, newPosition.Z, 0);
            pointList[0].Position = newPosition;
            pointList[1].Position = newPosition;
            pointList[2].Position = newPosition;
            pointList[3].Position = newPosition;
            opacity = newOpacity;
        }

        public void render(GraphicsDevice graphics, Matrix view, Matrix projection)
        {
            for (int j = 0; j < pointList.Length; j++) {
                pointList[j].Offset.X = 0;
                pointList[j].Offset.Y = 0;
                pointList[j].Offset.Z = 0;
            }

            graphics.VertexDeclaration = vertexDeclaration;

            billboardEffect.CurrentTechnique = billboardEffect.Techniques["Billboard"];
            billboardEffect.Parameters["World"].SetValue(Matrix.Identity);
            billboardEffect.Parameters["View"].SetValue(view);
            billboardEffect.Parameters["Projection"].SetValue(projection);
            billboardEffect.Parameters["boxTexture"].SetValue(box);
            billboardEffect.Parameters["heartEmptyTexture"].SetValue(heartEmpty);
            billboardEffect.Parameters["heartFullTexture"].SetValue(heartFull);
            billboardEffect.Parameters["waterEmptyTexture"].SetValue(waterEmpty);
            billboardEffect.Parameters["waterFullTexture"].SetValue(waterFull);
            billboardEffect.Parameters["xPosition"].SetValue(position);
            billboardEffect.Parameters["opacity"].SetValue(opacity);

            billboardEffect.Begin();
            EffectPass pass;
            
            pass = billboardEffect.CurrentTechnique.Passes["Box"];
            pass.Begin();
            graphics.DrawUserIndexedPrimitives<InfoBoxVertex>(
                PrimitiveType.TriangleList, pointList, 0, 4, indices, 0, 2);
            pass.End();
            
            for (int j = 0; j < pointList.Length; j++) {
                pointList[j].Offset.X = -6.75f;
                pointList[j].Offset.Y = -1.5f;
                pointList[j].Offset.Z = .01f;
            }

            int hearts = 0;
            bool nextRow = false;
            while (hearts < fullHearts) {
                if (hearts >= 10 && !nextRow) {
                    nextRow = true;
                    for (int j = 0; j < pointList.Length; j++) {
                        pointList[j].Offset.X = -6.75f;
                        pointList[j].Offset.Y = 0;
                    }
                }
                pass = billboardEffect.CurrentTechnique.Passes["HeartFull"];
                pass.Begin();
                graphics.DrawUserIndexedPrimitives<InfoBoxVertex>(
                PrimitiveType.TriangleList, pointList, 0, 4, indices, 0, 2);
                pass.End();
                hearts++;
                for (int j = 0; j < pointList.Length; j++ ) {
                    pointList[j].Offset.X += 1.5f;
                }
            }
            
            while (hearts < totalHearts) {
                if (hearts >= 10 && !nextRow) {
                    nextRow = true;
                    for (int j = 0; j < pointList.Length; j++) {
                        pointList[j].Offset.X = -6.75f;
                        pointList[j].Offset.Y = 0;
                    }
                }
                pass = billboardEffect.CurrentTechnique.Passes["HeartEmpty"];
                pass.Begin();
                graphics.DrawUserIndexedPrimitives<InfoBoxVertex>(
                    PrimitiveType.TriangleList, pointList, 0, 4, indices, 0, 2);
                pass.End();
                hearts++;
                for (int j = 0; j < pointList.Length; j++) {
                    pointList[j].Offset.X += 1.5f;
                }
            }

            for (int j = 0; j < pointList.Length; j++) {
                pointList[j].Offset.X = -6.75f;
                pointList[j].Offset.Y = 1.5f;
            }

            int water = 0;
            while (water < fullWater) {
                pass = billboardEffect.CurrentTechnique.Passes["WaterFull"];
                pass.Begin();
                graphics.DrawUserIndexedPrimitives<InfoBoxVertex>(
                PrimitiveType.TriangleList, pointList, 0, 4, indices, 0, 2);
                pass.End();
                water++;
                for (int j = 0; j < pointList.Length; j++) {
                    pointList[j].Offset.X += 1.5f;
                }
            }

            while (water < totalWater) {
                pass = billboardEffect.CurrentTechnique.Passes["WaterEmpty"];
                pass.Begin();
                graphics.DrawUserIndexedPrimitives<InfoBoxVertex>(
                    PrimitiveType.TriangleList, pointList, 0, 4, indices, 0, 2);
                pass.End();
                water++;
                for (int j = 0; j < pointList.Length; j++) {
                    pointList[j].Offset.X += 1.5f;
                }
            }

            billboardEffect.End();
        }
    }
}
