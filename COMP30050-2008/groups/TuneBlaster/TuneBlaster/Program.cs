using System;

namespace TuneBlaster_
{
    static class Program
    {
        /// <summary>
        /// Runs the game
        /// Default Class
        /// </summary>
        static void Main(string[] args)
        {
            using (Engine game = new Engine())
            {
                game.Run();
            }
        }
    }
}

