using System.IO;
using Microsoft.Xna.Framework;

namespace Drought
{
    class TextureMap
    {
        Vector4[,] map;
        int width, height;

        string fileName;

        public TextureMap(string fileName)
        {
            this.fileName = fileName;
        }


        public void initalise()
        {
            FileStream fs = new FileStream(fileName, FileMode.Open, FileAccess.Read);
            BinaryReader r = new BinaryReader(fs);

            r.BaseStream.Seek(10, SeekOrigin.Current);
            int bitmapOffset = (int)r.ReadUInt32();

            r.BaseStream.Seek(4, SeekOrigin.Current);
            width = (int)r.ReadUInt32();
            height = (int)r.ReadUInt32();

            map = new Vector4[width, height];

            r.BaseStream.Seek(bitmapOffset - 26, SeekOrigin.Current);

            Vector4 textureWeights;
            for (int x = 0; x < height; x++)
            {
                for (int y = 0; y < width; y++)
                {
                    int blueValue  = (int)r.ReadByte();
                    int greenValue = (int)r.ReadByte();
                    int redValue   = (int)r.ReadByte();

                    textureWeights = Vector4.Normalize(new Vector4(blueValue, redValue, greenValue, 0));
                    
                    map[width - y - 1, height - x - 1] = textureWeights;
                }
            }
            r.Close();
        }

        public Vector4 getValue(float x, float y)
        {
            return map[(int)x, (int)y];
        }
    }
}
