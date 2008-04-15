using System;
using System.Collections.Generic;
using System.Text;
using Microsoft.Xna.Framework;
using Microsoft.Xna.Framework.Graphics;
using Microsoft.Xna.Framework.Content;

namespace Drought.World
{
    class PlaneParticleEmitter
    {
        /*
         * Effect file used to render the particles
         */
        private Effect effect;

        /*
         * Random number generator to randomise the initial velocities.
         */
        private Random random;

        /*
         * Array of particles/Vertices
         */
        private Particle[] particles;

        /*
         * Emitters Position
         */
        private Vector3 position;

        /* 
         * Particles Initial Velocity
         */
        private Vector3 initialVelocity;

        /*
         * Proper gravity
         * Not just the downward type
         */
        private Vector3 gravity;

        /*
         * Colour of the particles
         */
        private Vector4 colour;

        /*
         * Total Number of Particles
         */
        private int numberOfParticles;

        /*
         * How long a particle lives for
         */
        private float lifeTime;

        /*
         * Index to the first active particle in the array
         */
        private int offset;

        /*
         * Current timeStep
         */
        private float timeStep;

        private int width;

        private int height;

        public PlaneParticleEmitter(int width, int height, Vector3 position, 
            Vector3 initialVelocity, Vector3 gravity, 
            Vector4 colour, 
            int numberOfParticles, float lifeTime)
        {
            this.width = width;
            this.height = height;

            this.colour = colour;
            this.position = position;
            this.gravity = gravity;
            this.initialVelocity = initialVelocity;
            this.numberOfParticles = numberOfParticles;
            this.lifeTime = lifeTime;

            initialize();
        }

        public void initialize()
        {
            timeStep = 0;
            offset = numberOfParticles;

            random = new Random();

            particles = new Particle[2*numberOfParticles];
            for (int i = 0; i < particles.Length; i+=2)
            {
                particles[i] = new Particle();
                particles[i].position.X = (position.X - width / 2) + width * (float)random.NextDouble();
                particles[i].position.Y = (position.Y - height / 2) + height * (float)random.NextDouble();
                particles[i].position.Z = position.Z;
                
                particles[i].velocity = initialVelocity;
                
                particles[i].gravity = gravity;

                particles[i].lifeTime = lifeTime;

                particles[i].colour = colour;
                particles[i].colour.W = 0.5f * (1.0f + (float)random.NextDouble());

                particles[i].size = 10;

                particles[i].startTime = -1;

                particles[i].id = i;

                particles[i + 1] = particles[i];
                particles[i + 1].id = i + 1;
            }
        }

        public void loadContent(ContentManager content)
        {
            effect = content.Load<Effect>("EffectFiles/rain");
        }

        public void addParticle()
        {
            if (offset > 0)
            {
                offset--;
                particles[offset * 2].startTime = timeStep;
                particles[(offset * 2) + 1].startTime = timeStep;
            }
        }

        public void addParticle(int numberOfNewParticles)
        {
            if (offset - numberOfParticles < 0)
            {
                numberOfNewParticles = offset;
            }

            offset -= numberOfNewParticles;

            for (int i = 0; i < numberOfNewParticles; i++)
            {
                particles[(offset * 2) + i].startTime = timeStep;
            }
        }

        public void update(GameTime gameTime)
        {
            timeStep += (float)(1.0f / 60.0f);
            addParticle(); addParticle(); 
        }

        public void render(GraphicsDevice graphics, Matrix viewMatrix, Matrix projectionMatrix)
        {
            if (offset < numberOfParticles)
            {

                graphics.RenderState.AlphaBlendEnable = true;
                graphics.RenderState.SourceBlend = Blend.One;
                graphics.RenderState.DestinationBlend = Blend.One;

                effect.CurrentTechnique = effect.Techniques["SimpleParticle"];
                effect.Parameters["World"].SetValue(Matrix.Identity);
                effect.Parameters["View"].SetValue(viewMatrix);
                effect.Parameters["Projection"].SetValue(projectionMatrix);

                effect.Parameters["timeStep"].SetValue(timeStep);

                effect.Begin();

                foreach (EffectPass pass in effect.CurrentTechnique.Passes)
                {
                    pass.Begin();

                    graphics.VertexDeclaration = new VertexDeclaration(graphics, Particle.VertexElements);

                    graphics.DrawUserPrimitives<Particle>(PrimitiveType.LineList, particles, offset * 2, numberOfParticles - offset);

                    pass.End();

                }
                effect.End();
            }
        }

    }
}
