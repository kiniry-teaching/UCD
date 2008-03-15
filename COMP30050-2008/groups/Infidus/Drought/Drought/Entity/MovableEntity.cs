using System;
using System.Collections.Generic;
using System.Text;
using Microsoft.Xna.Framework;
using Drought.World;
using Microsoft.Xna.Framework.Graphics;
using Microsoft.Xna.Framework.Content;
using Drought.Graphics;

namespace Drought.Entity
{

    class MovableEntity
    {
        private Vector3 position;

        private float velocity;

        private Vector3 heading;

        private NormalMap normalMap;

        private HeightMap heightMap;

        private Path path;

        private Model3D model;

        public MovableEntity(NormalMap normalMap, HeightMap heightMap, Model3D model)
        {
            position = new Vector3(256, 128, 15);
            heading = new Vector3(0, 0, 0);
            List<Vector3> nodes = new List<Vector3>();
            nodes.Add(position);
            path = new Path(nodes);
            velocity = 0.5f;
            this.normalMap = normalMap;
            this.heightMap = heightMap;
            this.model = model;
        }

        public void move()
        {
            if (!path.isFinished())
            {
                path.addDistance(velocity);
                position = path.getPosition();
            }
        }

        public void setPath(Path path)
        {
            this.path = path;
        }

        public void update()
        {
            move();
        }

        public void render(GraphicsDevice graphics)
        {
            model.render(graphics);
        }
    }
}
