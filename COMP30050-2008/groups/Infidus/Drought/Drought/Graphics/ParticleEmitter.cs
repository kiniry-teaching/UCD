using System;
using System.Collections.Generic;
using System.Text;
using Microsoft.Xna.Framework;
using Microsoft.Xna.Framework.Graphics;
using Microsoft.Xna.Framework.Content;

namespace Drought.Graphics
{
    struct Particle
    {
        public Vector3 position;
        public Vector3 velocity;
        public Vector3 gravity;

        public Vector4 colour;
        public float size;

        public float lifeTime;
        public float startTime;

        public float id;

        public static int SizeInBytes = (3 + 3 + 3 + 4 + 1 + 1 + 1 + 1) * sizeof(float);

        public static VertexElement[] VertexElements = new VertexElement[]
              {
                  new VertexElement( 0, 0, VertexElementFormat.Vector3, VertexElementMethod.Default, VertexElementUsage.Position, 0 ),
                  new VertexElement( 0, sizeof(float) * 3, VertexElementFormat.Vector3, VertexElementMethod.Default, VertexElementUsage.TextureCoordinate, 0 ),
                  new VertexElement( 0, sizeof(float) * 6, VertexElementFormat.Vector3, VertexElementMethod.Default, VertexElementUsage.TextureCoordinate, 1 ),
                  new VertexElement( 0, sizeof(float) * 9, VertexElementFormat.Vector4, VertexElementMethod.Default, VertexElementUsage.Color, 0 ),
                  new VertexElement( 0, sizeof(float) * 13, VertexElementFormat.Single, VertexElementMethod.Default, VertexElementUsage.PointSize, 2 ),
                  new VertexElement( 0, sizeof(float) * 14, VertexElementFormat.Single, VertexElementMethod.Default, VertexElementUsage.TextureCoordinate, 2 ),
                  new VertexElement( 0, sizeof(float) * 15, VertexElementFormat.Single, VertexElementMethod.Default, VertexElementUsage.TextureCoordinate, 3 ),
                  new VertexElement( 0, sizeof(float) * 16, VertexElementFormat.Single, VertexElementMethod.Default, VertexElementUsage.TextureCoordinate, 4 )
              };
    }

    class ParticleEmitter
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
         * How much we should vary the initial velocities by
         */
        private float chaosity;

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

        public ParticleEmitter(Vector3 position, Vector3 initialVelocity, Vector3 gravity, Vector4 colour, int numberOfParticles, float chaosity, float lifeTime)
        {
            this.colour = colour;
            this.position = position;
            this.gravity = gravity;
            this.initialVelocity = initialVelocity;
            this.numberOfParticles = numberOfParticles;
            this.chaosity = chaosity;
            this.lifeTime = lifeTime;
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
                particles[i].position = position;
                
                particles[i].velocity = initialVelocity;
                
                if (initialVelocity != Vector3.Zero)
                {
                    particles[i].velocity.X += (float)random.NextDouble() * (float)random.NextDouble() * chaosity;
                    particles[i].velocity.Y += (float)random.NextDouble() * (float)random.NextDouble() * chaosity;
                    particles[i].velocity.Z += (float)random.NextDouble() * (float)random.NextDouble() * chaosity;
                }

                if (random.NextDouble() < 0.5)
                    particles[i].velocity.X = -particles[i].velocity.X;
                if (random.NextDouble() < 0.5)
                    particles[i].velocity.Y = -particles[i].velocity.Y;

                particles[i].gravity = gravity;

                particles[i].lifeTime = lifeTime;

                particles[i].colour = colour;

                particles[i].size = 1000;

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

        public void update(GameTime gameTime)
        {
            timeStep += (float)(1.0f / 60.0f);
            addParticle();
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
