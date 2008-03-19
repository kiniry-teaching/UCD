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

        private Matrix orientation;

        private float velocity;

        private Path path;

        private Model3D model;

        private bool selected, oldSelected;

        public MovableEntity(Model3D model, Path path)
        {
            this.path = path;
            position = path.getPosition();
            prevPosition = path.getPosition();
            heading = new Vector3(0, 0, 0);
            rotation = new Vector3(0, 0, 0);
            normal = path.getNormal();
            orientation = Matrix.Identity;
            velocity = 0.05f;
            this.model = model;
            selected = false;
            oldSelected = false;
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

                //Console.WriteLine(normal);
                /*
                rotation.X = (float)Math.Atan2(normal.Y, normal.Z);
                rotation.Y = (float)Math.Atan2(normal.X, normal.Z);
                rotation.Z = (float)Math.Atan2(heading.Y, heading.X);
                */

                orientation = Matrix.CreateRotationZ((float)Math.Atan2(heading.Y, heading.X));
                //Console.WriteLine("mz " + orientation);
                orientation.Up = normal;
                orientation.Right = Vector3.Cross(orientation.Forward, orientation.Up);
                orientation.Right = Vector3.Normalize(orientation.Right);
                orientation.Forward = Vector3.Cross(orientation.Up, orientation.Right);
                orientation.Forward = Vector3.Normalize(orientation.Forward);

                if (selected && !oldSelected) {
                    Console.WriteLine("selected!");
                }
                if (!selected && oldSelected) {
                    Console.WriteLine("unselected!");
                }
                oldSelected = selected;
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
            //position.Z += 10;
            model.position = position;
            model.rotationAngles = rotation;
            //Console.WriteLine("heading:" + heading + " normal:" + normal + " rotation:"+model.rotationAngles);
            Matrix orientation = Matrix.Identity;
            if (selected) {
                model.render(graphics, orientation, position + new Vector3(0, 0, 20));
            }
            else {
                model.render(graphics, orientation, position);
            }
        }

        public Vector3 getPosition() {
            return position;
        }

        public void setSelected(bool selected) {
            this.selected = selected;
        }

        public bool isSelected() {
            return selected;
        }
    }
}
