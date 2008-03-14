using System;
using System.Collections.Generic;
using Microsoft.Xna.Framework;

namespace Drought
{
    public class Camera
    {
        private Game game;
        private HeightMap heightMap;

        private Vector3 eyeVector;
        private Vector3 focusVector;
        private Vector3 upVector;

        private Vector3 cameraRotationAngles;

        private float cameraStand = 10.0f;
        private float angleIncrement = 0.025f;

        public Camera(Game game, HeightMap heightMap)
        {
            this.game = game;
            this.heightMap = heightMap;
        }

        public void Initialize()
        {
            eyeVector   = new Vector3(0, 0, heightMap.getHeight(0, 0));
            focusVector = new Vector3(0, 0, heightMap.getHeight(0, 0));
            upVector    = new Vector3(0, 0, 1);

            cameraRotationAngles = new Vector3(MathHelper.PiOver4, 0, MathHelper.PiOver4);
        }

        public void Update(GameTime gameTime)
        {
            if (eyeVector.Z < heightMap.getHeight(eyeVector.X, eyeVector.Y) + cameraStand)
                eyeVector.Z = heightMap.getHeight(eyeVector.X, eyeVector.Y) + cameraStand;

            Matrix cameraRotation = Matrix.CreateRotationX(cameraRotationAngles.X) * Matrix.CreateRotationZ(cameraRotationAngles.Z);
            focusVector = eyeVector + Vector3.Transform(new Vector3(0, 1, 0), cameraRotation);
            upVector = Vector3.Transform(new Vector3(0, 0, 1), cameraRotation);
        }

        public Matrix getViewMatrix()
        {
            return Matrix.CreateLookAt(eyeVector, focusVector, upVector);
        }

        public Matrix getProjectionMatrix()
        {
            return Matrix.CreatePerspectiveFieldOfView(MathHelper.PiOver4, game.Window.ClientBounds.Width / game.Window.ClientBounds.Height, 1.0f, 500.0f); ;
        }

        public void forward()
        {
            Vector3 forward = focusVector - eyeVector;
            forward.Z = 0;
            forward.Normalize();

            eyeVector.X += forward.X * 0.5f;
            eyeVector.Y += forward.Y * 0.5f;
        }

        public void back()
        {
            Vector3 forward = focusVector - eyeVector;
            forward.Z = 0;
            forward.Normalize();

            eyeVector.X -= forward.X * 0.5f;
            eyeVector.Y -= forward.Y * 0.5f;
        }

        public void left()
        {
            Vector3 forward = focusVector - eyeVector;
            forward.Z = 0;
            forward.Normalize();

            eyeVector.X -= forward.Y * 0.5f;
            eyeVector.Y += forward.X * 0.5f;
        }

        public void right()
        {
            Vector3 forward = focusVector - eyeVector;
            forward.Z = 0;
            forward.Normalize();

            eyeVector.X += forward.Y * 0.5f;
            eyeVector.Y -= forward.X * 0.5f;
        }

        public void ascend()
        {
            eyeVector.Z += 1;
        }


        public void descend()
        {
            eyeVector.Z -= 1;
        }

        public void zoomOut()
        {
            Vector3 forward = focusVector - eyeVector;
            forward *= 2f;
            eyeVector = focusVector - forward;
        }

        public void zoomIn()
        {
            Vector3 forward = focusVector - eyeVector;            
            forward *= -2f;
            eyeVector = focusVector - forward;
        }

        public void rotateUp()
        {
            if (cameraRotationAngles.X < 0)
                cameraRotationAngles.X += angleIncrement;
        }

        public void rotateDown()
        {
            if (cameraRotationAngles.X > -Math.PI*9 /20)
               cameraRotationAngles.X -= angleIncrement;
        }


        public void rotateRight()
        {
            cameraRotationAngles.Z -= angleIncrement;
        }

        public void rotateLeft()
        {
            cameraRotationAngles.Z += angleIncrement;
        }

        public void orbitRight()
        {
            throw new NotImplementedException("Based on a design decision");
        }

        public void orbitLeft()
        {
            throw new NotImplementedException("Based on a design decision");
        }

        public void orbitUp()
        {
            throw new NotImplementedException("Based on a design decision");
        }

        public void orbitDown()
        {
            throw new NotImplementedException("Based on a design decision");
        }
    }
}