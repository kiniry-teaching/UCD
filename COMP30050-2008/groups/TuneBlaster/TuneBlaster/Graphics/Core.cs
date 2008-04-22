using System;
using System.Collections.Generic;
using System.Text;
using Microsoft.Xna.Framework.Input;
using Microsoft.Xna.Framework.Graphics;
using Microsoft.Xna.Framework.Storage;
using Microsoft.Xna.Framework;




// Author Hugh, Ahmed

namespace TuneBlaster_.Graphics
{
    class Core : Image
    {
        #region Fields (ballsSize, oldRotation, acceleration, balls, maxAcceleration)

        Game game;
        public int ballsSize, looseBallsSize;
        float oldRotation;
        public float acceleration;
        public List<FixedBall> balls;
        public List<MovingBall> looseBalls;
        static float maxAcceleration = 0.05f;
        KeyboardState keyState;
        GamePadState padState;
        value colour;
        Vector3 pos;
        public bool searchLightOn;
        Image searchLight;
        Texture2D searchLightTexture;
        public bool blackwhite;
        int nextSpecial;
        bool gameOver;


        #endregion

        #region Main Methods (Core, Initialise, Draw, Update)

        /*
         * Constructor for core
         */
        public Core()
        {
            balls = new List<FixedBall>();
            looseBalls = new List<MovingBall>();
            searchLight = new Image();
        }

        /*
         * Initialise start values
         */
        public override void Initialise(Vector2 mySize, Vector2 myPosition, Game g)
        {
            base.Initialise(mySize, myPosition, g);
            acceleration = 0f;
            oldRotation = 0f;
            gameOver = false;
            game = g;
            nextSpecial = 0;
            searchLight.Initialise(new Vector2(1200, 1200), Position, g);
            searchLightOn = false;
        }

        /*
         * Draw on the spritebatch for each frame
         */
        public override void Draw(GameTime gameTime)
        {
            base.Draw(gameTime);
            for (int i = 0; i < ballsSize; i++)
            {
                balls[i].Draw(gameTime);
            }

            for (int i = 0; i < looseBallsSize; i++)
            {
                looseBalls[i].Draw(gameTime);
            }
        }

        /*
         * Update variables for each frame
         */

        public value Update(GameTime gameTime, KeyboardState keyBoardState, GamePadState gamePadState)
        {
            colour = value.none;
            for (int i = ballsSize - 1; i >= 0; i--)
            {
                if (balls[i] != null)
                {
                    if (balls[i].coreDistance > 310)
                    {
                        gameOver = true;
                        return colour;
                    }
                    if (balls[i].IsDead())
                    {
                        colour = balls[i].colour;
                        balls.Remove(balls[i]);
                        ballsSize--;
                    }
                }
            }
            Move(keyBoardState, gamePadState);

            
            return colour;
        }

        #endregion

        #region Action Methods (Move, AddBall, CheckLoose, UpdateLoose, CheckExplosions)

        /*
         * Move the core based on the input
         */
        public void Move(KeyboardState keyBoardState, GamePadState gamePadState)
        {
            oldRotation = rotation;
            SetKeyboardRotation(keyBoardState);
            SetControllerRotation(gamePadState);
            for (int i = 0; i < ballsSize; i++)
            {
                balls[i].Move(rotation - oldRotation);
            }
            CheckLoose();

            for (int i = 0; i < looseBallsSize; i++)
            {
                looseBalls[i].Move();
            }
            CheckLoose();
            
            if (keyBoardState.IsKeyDown(Keys.A))
            {
                NextSpecial();
            }

            if (keyBoardState.IsKeyDown(Keys.S))
            {
                ResetSpecial();
            }

            if (keyBoardState.IsKeyDown(Keys.Q))
            {
                BlackWhite();
            }

            if (keyBoardState.IsKeyDown(Keys.W))
            {
                Colour();
            }

            if (searchLightOn)
            {
                MoveSearchLight(keyBoardState, gamePadState);
            }
        }

        public override void LoadGraphicsContent(SpriteBatch spriteBatch, Texture2D texture)
        {
            this.spriteBatch = spriteBatch;
            this.texture = texture;
            searchLightTexture = game.Content.Load<Texture2D>(@"Resources\Textures\light1");
            searchLight.LoadGraphicsContent(spriteBatch, searchLightTexture);
        }


        public void BlackWhite()
        {
            texture = game.Content.Load<Texture2D>(@"Resources\Textures\graynew-core");
            blackwhite = true;
        }

        public void Colour()
        {
            texture = game.Content.Load<Texture2D>(@"Resources\Textures\Core");
            blackwhite = false;
        }



        /*
         * Add a ball to the core's ball list
         */
        public void AddBall(FixedBall f)
        {
            balls.Add(f);
            ballsSize++;
            CheckExplosions();
            UpdateLoose();
        }

        /*
         * Remove any loose balls that have become fixed
         * */
        public void CheckLoose()
        {
            for (int i = 0; i < looseBallsSize; i++)
            {
                if (!looseBalls[i].IsLive())
                {
                    looseBalls.RemoveAt(i);
                    looseBallsSize--;
                }
            }
        }

        public void UpdateLoose()
        {
            for (int i = 0; i < ballsSize; i++)
            {
                balls[i].CheckSupports();
            }
            bool redo = false;
            for (int i = 0; i < ballsSize; i++)
            {
                if (!balls[i].IsAgainstCore() && balls[i].Unsupported() && !balls[i].IsDead())
                {
                    redo = true;
                    MovingBall m = new MovingBall(this, balls[i].colour);
                    m.Initialise(balls[i].Size, balls[i].Position, this.game);
                    m.LoadGraphicsContent(balls[i].spriteBatch, balls[i].colourTexture);
                    balls[i].Destroy();
                    balls.Remove(balls[i]);
                    ballsSize--;
                    looseBalls.Add(m);
                    looseBallsSize++;
                }
            }
            if (redo == true)
            {
                UpdateLoose();
            }
        }

        /*
         * Check each ball as an explosion candidate, destroying if necessary
         */
        public void CheckExplosions()
        {
            Vector3 ballSound;
            Vector2 where;

            for (int i = 0; i < ballsSize; i++)
            {
                if (balls[i] != null)
                {
                    if (balls[i].numInContact > 2)
                    {
                        balls[i].Destroy();

                        where.X = balls[i].Position.X;
                        where.Y = balls[i].Position.Y;

                        ballSound = new Vector3(where.X, where.Y, 0f);
                        setPos(ballSound);

                                if(balls[i].colour== Image.value.red){
                                    Engine.redblast.AddParticles(where);
                                    Engine.smoke.AddParticles(where);
                                    Engine.explosion.AddParticles(where);
                                    Engine.Rnote.AddParticles(where);

                                }
                                if (balls[i].colour == Image.value.green)
                                {
                                    Engine.greenblast.AddParticles(where);
                                    Engine.smoke.AddParticles(where);
                                    Engine.explosion.AddParticles(where);
                                    Engine.Gnote.AddParticles(where);

                                }
                                if (balls[i].colour == Image.value.purple)
                                {
                                    Engine.purpleblast.AddParticles(where);
                                    Engine.smoke.AddParticles(where);
                                    Engine.explosion.AddParticles(where);
                                    Engine.Pnote.AddParticles(where);

                                }
                                if (balls[i].colour == Image.value.blue)
                                {

                                    Engine.blueblast.AddParticles(where);
                                    Engine.smoke.AddParticles(where);
                                    Engine.explosion.AddParticles(where);
                                    Engine.Bnote.AddParticles(where);

                                }
                        Engine.Score++;
                        Engine.blast = true;
                        Engine.blastTime = 30;
                       

                        //to put in code for explosion

                    }
                }
            }
        }

        public void setPos(Vector3 v)
        {
            pos = v;
        }

        public Vector3 getPos()
        {
            return pos;
        }

        /*
         * Turn on the designated next special mode
         * */
        public void NextSpecial()
        {
            if (nextSpecial % 2 == 1)
            {
                BlackWhite();
            }
            else
            {
                searchLightOn = true;
            }
            nextSpecial++;
        }

        /*
         * Turn the current Special Mode off 
         * */
        public void ResetSpecial()
        {
            if (blackwhite)
            {
                Colour();
            }
            else
            {
                searchLightOn = false;
            }
        }

        /*
         * Turn the current Special Mode off 
         * */
        public bool GameOver()
        {
            return gameOver;
        }




        #endregion

        #region Input Methods (SetControllerRotation, SetKeyBoardRotation)

        /*
         * Set a new rotation based on controller input
         */
        public void SetControllerRotation(GamePadState gamePadState)
        {
            if (gamePadState.ThumbSticks.Left.X < 0.0f)
            {
                acceleration -= 0.01f * gamePadState.Triggers.Right;
                acceleration *= 0.9f;

                if (acceleration >= maxAcceleration)
                {
                    acceleration = maxAcceleration;
                }
            }
            else if (gamePadState.ThumbSticks.Left.X > 0.0f)
            {
                acceleration += 0.01f * gamePadState.Triggers.Right;
                acceleration *= 0.9f;

                if (acceleration <= -maxAcceleration)
                {
                    acceleration = -maxAcceleration;
                }
            }
            else
            {
                acceleration *= 0.9f;
            }

            rotation += acceleration;
        }

        /*
         * Set a new rotation based on Keyboard input
         */
        public void SetKeyboardRotation(KeyboardState keyBoardState)
        {
            if (keyBoardState.IsKeyDown(Keys.Right))
            {
                if (keyBoardState.IsKeyDown(Keys.Left))
                {
                    acceleration *= 0.90f;
                }
                acceleration = 0.03f;
            }
            if (keyBoardState.IsKeyDown(Keys.Left))
            {
                acceleration = -0.03f;
            }
            else
            {
                acceleration *= 0.9f;
            }

            rotation += acceleration;

        }

        public void DrawSearchLight(GameTime gameTime)
        {
            if (searchLightOn)
            {
                searchLight.Draw(gameTime);
            }
        }


        public void MoveSearchLight(KeyboardState keyboard, GamePadState gamepad)
        {

            if (keyboard.IsKeyDown(Keys.Up)) 
            {
                searchLight.Position = new Vector2(searchLight.Position.X, searchLight.Position.Y - 1);
            }

            float tempX = gamepad.ThumbSticks.Right.X*10;
            float tempy = gamepad.ThumbSticks.Right.Y*10;

            searchLight.Position = new Vector2(searchLight.Position.X + tempX, searchLight.Position.Y - tempy);

            if (Vector2.Distance(Position, searchLight.Position) > 230) 
            {
                Vector2 d = Position - searchLight.Position;
                d.Normalize();
                d = d * 230;
                searchLight.Position = Position - d;
            }
        }

        #endregion
    }
}
