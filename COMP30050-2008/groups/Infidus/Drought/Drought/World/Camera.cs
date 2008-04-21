using System;
using System.Collections.Generic;
using Microsoft.Xna.Framework;
using Drought.State;

namespace Drought.World
{
    class Camera
    {
        private GameState gameState;
        private LevelInfo levelInfo;

        private Vector3 eyeVector;
        private Vector3 focusVector;
        private Vector3 upVector;

        private Vector3 cameraRotationAngles;

        private float cameraStand = 10.0f;
        private float angleIncrement = 0.025f;

        private bool isRestricted;

        public Camera(GameState gameState, LevelInfo levelInfo, bool isRestricted)
        {
            this.gameState = gameState;
            this.levelInfo = levelInfo;
            this.isRestricted = isRestricted;

            initialize();
        }

        public void initialize()
        {
            cameraRotationAngles = new Vector3(0, 0, -35 * angleIncrement);
            Matrix cameraRotation = Matrix.CreateRotationX(cameraRotationAngles.X) * Matrix.CreateRotationZ(cameraRotationAngles.Z);

            eyeVector   = new Vector3(0.0f, 0.0f, levelInfo.getHeight(0, 0)+cameraStand);
            focusVector = eyeVector + Vector3.Transform(new Vector3(0, 1, 0), cameraRotation);
            upVector    = new Vector3(0, 0, 1);
        }

        public void update()
        {
            if (isRestricted && eyeVector.Z < levelInfo.getHeight(eyeVector.X, eyeVector.Y) + cameraStand)
                eyeVector.Z = levelInfo.getHeight(eyeVector.X, eyeVector.Y) + cameraStand;

            Matrix cameraRotation = Matrix.CreateRotationX(cameraRotationAngles.X) * Matrix.CreateRotationZ(cameraRotationAngles.Z);
            focusVector = eyeVector + Vector3.Transform(new Vector3(0, 1, 0), cameraRotation);
            upVector = Vector3.Transform(new Vector3(0, 0, 1), cameraRotation);
        }

        public Vector3 getPosition()
        {
            return eyeVector;
        }

        public float getOrientation()
        {
            return cameraRotationAngles.Z;
        }

        public Matrix getViewMatrix()
        {
            return Matrix.CreateLookAt(eyeVector, focusVector, upVector);
        }

        public Matrix getProjectionMatrix()
        {
            return Matrix.CreatePerspectiveFieldOfView(MathHelper.PiOver4, gameState.getGraphics().Viewport.Width / gameState.getGraphics().Viewport.Height, 1.0f, 50000.0f); ;
        }

        public void forward()
        {
            Vector3 forward = focusVector - eyeVector;
            forward.Z = 0;
            forward.Normalize();

            eyeVector.X += forward.X * 0.5f;
            eyeVector.Y += forward.Y * 0.5f;

            focusVector.X += forward.X * 0.5f;
            focusVector.Y += forward.Y * 0.5f;
        }

        public void back()
        {
            Vector3 forward = focusVector - eyeVector;
            forward.Z = 0;
            forward.Normalize();
            
            eyeVector.X -= forward.X * 0.5f;
            eyeVector.Y -= forward.Y * 0.5f;

            focusVector.X -= forward.X * 0.5f;
            focusVector.Y -= forward.Y * 0.5f;
        }

        public void left()
        {
            Vector3 forward = focusVector - eyeVector;
            forward.Z = 0;
            forward.Normalize();
            
            eyeVector.X -= forward.Y * 0.5f;
            eyeVector.Y += forward.X * 0.5f;

            focusVector.X -= forward.Y * 0.5f;
            focusVector.Y += forward.X * 0.5f;
        }

        public void right()
        {
            Vector3 forward = focusVector - eyeVector;
            forward.Z = 0;
            forward.Normalize();
 
            eyeVector.X += forward.Y * 0.5f;
            eyeVector.Y -= forward.X * 0.5f;

            focusVector.X += forward.Y * 0.5f;
            focusVector.Y -= forward.X * 0.5f;
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

            eyeVector -= forward;
            focusVector -= forward;
        }

        public void zoomIn()
        {
            Vector3 forward = focusVector - eyeVector;

            eyeVector += forward;
            focusVector += forward;
        }

        public void rotateUp()
        {
            if (!isRestricted || cameraRotationAngles.X < 0)
                cameraRotationAngles.X += angleIncrement;
        }

        public void rotateDown()
        {
            if (!isRestricted || cameraRotationAngles.X > -Math.PI*9 /20)
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
    }
}
