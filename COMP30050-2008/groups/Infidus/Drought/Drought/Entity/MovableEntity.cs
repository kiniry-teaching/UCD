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

        private Vector3 prevPosition;

        private Vector3 heading;

        private Vector3 rotation;

        private Vector3 normal;

        private Vector3 prevNormal;

        private float velocity;

        private Path path;

        private Model3D model;

        public MovableEntity(Model3D model, Path path)
        {
            this.path = path;
            position = path.getPosition();
            prevPosition = path.getPosition();
            heading = new Vector3(0, 0, 0);
            rotation = new Vector3(0, 0, 0);
            normal = path.getNormal();
            velocity = 0.05f;
            this.model = model;
        }

        public void move()
        {
            if (!path.isFinished())
            {
                path.addDistance(velocity);
                prevPosition.X = position.X;
                prevPosition.Y = position.Y;
                prevPosition.Z = position.Z;
                position = path.getPosition();
                prevNormal.X = normal.X;
                prevNormal.Y = normal.Y;
                prevNormal.Z = normal.Z;
                normal = path.getNormal();

                heading = Vector3.Subtract(position, prevPosition);
                //heading.Normalize();

                rotation.X = (float)-Math.Atan2(prevNormal.Y, normal.Z);
                rotation.Y = (float)Math.Atan2(normal.X, normal.Z);
                rotation.Z = (float)Math.Atan2(heading.Y, heading.X);
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
            model.position = position;
            model.rotationAngles = rotation;
            //Console.WriteLine("heading:" + heading + " normal:" + normal + " rotation:"+model.rotationAngles);
            model.render(graphics);
        }
    }
}
