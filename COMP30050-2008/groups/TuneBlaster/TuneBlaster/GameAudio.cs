#region Using Statements
using Microsoft.Xna.Framework;
using Microsoft.Xna.Framework.Audio;
using Microsoft.Xna.Framework.Content;
using Microsoft.Xna.Framework.Graphics;
using Microsoft.Xna.Framework.Input;
using Microsoft.Xna.Framework.Storage;
using System;
using System.Threading;
using System.Collections.Generic;
using TuneBlaster_.Graphics;
#endregion

namespace TuneBlaster_
{
    /// <summary>
    /// The class that manages the audio within the game
    /// Author Dermot Kirby
    /// </summary>
    class GameAudio
    {
        #region Fields (musicEngine, musicWaveBank, soundBanks, baseCues, pianoCues, stringCues, ballColour)

        private AudioEngine musicEngine;
        private WaveBank musicWaveBank;
        private SoundBank musicSoundBank, pianoBank, stringBank, bellBank, ballBank;

        Cue baseCue1, baseCue2;
        Cue pianoCue1, pianoCue2, pianoCue3, pianoCue4;
        Cue stringCue1, stringCue2, stringCue3, stringCue4;
        Cue bellCue1, bellCue2;
        Cue ballCue1;
        Image.value ballColour;

        public AudioListener listener;
        public AudioEmitter emitter;

        #endregion

        public GameAudio()
        {
            musicEngine = new AudioEngine("Content\\Audio\\Win\\Game Sounds.xgs");
            musicWaveBank = new WaveBank(musicEngine, "Content\\Audio\\Win\\Wave Bank.xwb");
            musicSoundBank = new SoundBank(musicEngine, "Content\\Audio\\Win\\Base Bank.xsb");
            //pianoBank = new SoundBank(musicEngine, "Content\\Audio\\Win\\Piano Bank.xsb");
            stringBank = new SoundBank(musicEngine, "Content\\Audio\\Win\\String Bank.xsb");
            bellBank = new SoundBank(musicEngine, "Content\\Audio\\Win\\Bell Bank.xsb");
            ballBank = new SoundBank(musicEngine, "Content\\Audio\\Win\\Ball Noise Bank.xsb");
            listener = new AudioListener();
            emitter = new AudioEmitter();
        }

        #region Initialisation Methods (Initialise, Cue Resetters)

        /// <summary>
        /// Plays the initial melody.
        /// </summary>
        public void Initialise()
        {
            resetBaseCues();
            resetBallCues();
            //resetPianoCues();
            resetStringCues();
            resetBellCues();
            baseCue1.Play();
        }

        /// <summary>
        /// Sets the cues equal to the specified files from the sound bank to make them ready to be played again.
        /// </summary>
        public void resetBallCues()
        {
            ballCue1 = ballBank.GetCue("Ball Noise 1");
        }

        /// <summary>
        /// Sets the cues equal to the specified files from the sound bank to make them ready to be played again.
        /// </summary>
        public void resetBaseCues()
        {
            baseCue1 = musicSoundBank.GetCue("Base Melody 1");
            baseCue2 = musicSoundBank.GetCue("Base Melody 2");
        }

        /// <summary>
        /// Sets the cues equal to the specified files from the sound bank to make them ready to be played again.
        /// </summary>
        public void resetPianoCues()
        {
            pianoCue1 = pianoBank.GetCue("Piano Melody 1");
            pianoCue2 = pianoBank.GetCue("Piano Melody 2");
            pianoCue3 = pianoBank.GetCue("Piano Melody 3");
            pianoCue4 = pianoBank.GetCue("Piano Melody 4");
        }

        /// <summary>
        /// Sets the cues equal to the specified files from the sound bank to make them ready to be played again.
        /// </summary>
        public void resetStringCues()
        {
            stringCue1 = stringBank.GetCue("String Melody 1");
            stringCue2 = stringBank.GetCue("String Melody 2");
            stringCue3 = stringBank.GetCue("String Melody 3");
            stringCue4 = stringBank.GetCue("String Melody 4");
        }
        /// <summary>
        /// Sets the cues equal to the specified files from the sound bank to make them ready to be played again.
        /// </summary>
        public void resetBellCues()
        {
            bellCue1 = bellBank.GetCue("Bell Melody 1");
            bellCue2 = bellBank.GetCue("Bell Melody 2");
        }

        #endregion

        #region Disposer Methods (disposePianoCues, disposeStringCues, disposeBellCues)

        /// <summary>
        /// Dispose of all the ball noise cues in memory
        /// </summary>
        public void disposeBallCues()
        {
            ballCue1.Dispose();
        }

        /// <summary>
        /// Dispose of all the piano cues in memory
        /// </summary>
        public void disposePianoCues()
        {
            pianoCue1.Dispose();
            pianoCue2.Dispose();
            pianoCue3.Dispose();
            pianoCue4.Dispose();
        }

        /// <summary>
        /// Dispose of all the string cues in memory
        /// </summary>
        public void disposeStringCues()
        {
            stringCue1.Dispose();
            stringCue2.Dispose();
            stringCue3.Dispose();
            stringCue4.Dispose();
        }
        /// <summary>
        /// Dispose of all the bell cues in memory
        /// </summary>
        public void disposeBellCues()
        {
            bellCue1.Dispose();
            bellCue2.Dispose();
        }

        #endregion

        #region Threads (InstrChanger, ChangeBase, ChangePiano, ChangeStrings, ChangeBells)

        /// <summary>
        /// Starts the thread for instrument modification depending on the colour.
        /// </summary>
        public void InstrChanger(Image.value colour)
        {
            disposeBallCues();
            resetBallCues();

            Console.Write("Listener: " + listener.Position + " Emitter: " + emitter.Position);
            ballCue1.Apply3D(listener, emitter);
            ballCue1.Play();

            Thread Alter = new Thread(new ParameterizedThreadStart(ChangeMelody));
            Alter.Start(colour);
        }

        /// <summary>
        /// Starts the thread for base melody modification.
        /// </summary>
        public void ChangeBase()
        {
            Thread Base = new Thread(new ThreadStart(ModifyBase));
            Base.Start();
        }

        /// <summary>
        /// Starts the thread for piano melody modification.
        /// </summary>
        public void ChangePiano()
        {
            Thread Pianos = new Thread(new ThreadStart(ModifyPiano));
            Pianos.Start();
        }

        /// <summary>
        /// Starts the thread for string melody modification.
        /// </summary>
        public void ChangeStrings()
        {
            Thread Strings = new Thread(new ThreadStart(ModifyStrings));
            Strings.Start();
        }

        /// <summary>
        /// Starts the thread for bell melody modification.
        /// </summary>
        public void ChangeBells()
        {
            Thread Bells = new Thread(new ThreadStart(ModifyBells));
            Bells.Start();
        }
        #endregion

        #region Melody Modifiers (ModifyBase, ModifyPiano, ModifyStrings, ModifyBells)
        /// <summary>
        /// Modifies the initial melody.
        /// </summary>
        public void ModifyBase()
        {
            if (baseCue1 != null && baseCue1.IsPlaying)
            {
                baseCue1.Stop(AudioStopOptions.AsAuthored);
                while (!baseCue1.IsStopped) { }
                resetBaseCues();
                baseCue2.Play();
            }

            else if (baseCue2 != null && baseCue2.IsPlaying)
            {
                baseCue2.Stop(AudioStopOptions.AsAuthored);
                while (!baseCue2.IsStopped) { }
                resetBaseCues();
                baseCue1.Play();
            }
        }

        /// <summary>
        /// Modifies the piano melody.
        /// </summary>
        public void ModifyPiano()
        {
            if (pianoCue1 != null && pianoCue1.IsPlaying)
            {
                pianoCue1.Stop(AudioStopOptions.AsAuthored);
                while (!pianoCue1.IsStopped) { }
                if (pianoCue1 != null && !pianoCue1.IsPlaying)
                {
                    pianoCue1.Dispose();
                    resetPianoCues();
                    pianoCue2.Play();
                }
            }

            else if (pianoCue2 != null && pianoCue2.IsPlaying)
            {
                pianoCue2.Stop(AudioStopOptions.AsAuthored);
                while (!pianoCue2.IsStopped) { }
                if (pianoCue2 != null && !pianoCue2.IsPlaying)
                {
                    pianoCue2.Dispose();
                    resetPianoCues();
                    pianoCue3.Play();
                }
            }

            else if (pianoCue3 != null && pianoCue3.IsPlaying)
            {
                pianoCue3.Stop(AudioStopOptions.AsAuthored);
                while (!pianoCue3.IsStopped) { }
                if (pianoCue3 != null && !pianoCue3.IsPlaying)
                {
                    pianoCue3.Dispose();
                    resetPianoCues();
                    pianoCue4.Play();
                }
            }

            else if (pianoCue4 != null && pianoCue4.IsPlaying)
            {
                pianoCue4.Stop(AudioStopOptions.AsAuthored);
                while (!pianoCue4.IsStopped) { }
                if (pianoCue4 != null && !pianoCue4.IsPlaying)
                {
                    pianoCue4.Dispose();
                    resetPianoCues();
                    pianoCue1.Play();
                }
            }
        }

        /// <summary>
        /// Modifies the string melody.
        /// </summary>
        public void ModifyStrings()
        {
            if (stringCue1 != null && stringCue1.IsPlaying)
            {
                stringCue1.Stop(AudioStopOptions.AsAuthored);
                while (!stringCue1.IsStopped) { }
                if (stringCue1 != null && !stringCue1.IsPlaying)
                {
                    stringCue1.Dispose();
                    resetStringCues();
                    stringCue2.Play();
                }
            }

            else if (stringCue2 != null && stringCue2.IsPlaying)
            {
                stringCue2.Stop(AudioStopOptions.AsAuthored);
                while (!stringCue2.IsStopped) { }
                if (stringCue2 != null && !stringCue2.IsPlaying)
                {
                    stringCue2.Dispose();
                    resetStringCues();
                    stringCue3.Play();
                }
            }

            else if (stringCue3 != null && stringCue3.IsPlaying)
            {
                stringCue3.Stop(AudioStopOptions.AsAuthored);
                while (!stringCue3.IsStopped) { }
                if (stringCue3 != null && !stringCue3.IsPlaying)
                {
                    stringCue3.Dispose();
                    resetStringCues();
                    stringCue4.Play();
                }
            }

            else if (stringCue4 != null && stringCue4.IsPlaying)
            {
                stringCue4.Stop(AudioStopOptions.AsAuthored);
                while (!stringCue4.IsStopped) { }
                if (stringCue4 != null && !stringCue4.IsPlaying)
                {
                    stringCue4.Dispose();
                    resetStringCues();
                    stringCue1.Play();
                }
            }
        }

        /// <summary>
        /// Modifies the bell melody.
        /// </summary>
        public void ModifyBells()
        {
            if (bellCue1 != null && bellCue1.IsPlaying)
            {
                bellCue1.Stop(AudioStopOptions.AsAuthored);
                while (!bellCue1.IsStopped) { }
                if (bellCue1 != null && !bellCue1.IsPlaying)
                {
                    bellCue1.Dispose();
                    resetBellCues();
                    bellCue2.Play();
                }
            }

            else if (bellCue2 != null && bellCue2.IsPlaying)
            {
                bellCue2.Stop(AudioStopOptions.AsAuthored);
                while (!bellCue2.IsStopped) { }
                if (bellCue2 != null && !bellCue2.IsPlaying)
                {
                    bellCue2.Dispose();
                    resetBellCues();
                    bellCue1.Play();
                }
            }
        }
        #endregion

        /// <summary>
        /// Method that regulates the modification of the song.
        /// </summary>
        public void ChangeMelody(Object colour)
        {
            ballColour = (Image.value)colour;
            ChangeBase();                                                                       // Base melody is modified every time balls are destroyed.

            // If the destoyed balls are blue
            if (ballColour == Image.value.blue)
            {
                // If the piano isn't playing
                if (!pianoCue1.IsPlaying && !pianoCue2.IsPlaying)
                {
                    // If there's a piano cue in memory, destroy it
                    if (pianoCue1 != null)
                    {
                        disposePianoCues();
                        resetPianoCues();
                    }

                    // Wait until the base melody has finished.
                    while (!baseCue1.IsStopped && !baseCue2.IsStopped)
                    {
                        // TO DO
                    }
                    pianoCue1.Play();                                                           // Play the piano now so that it is in sync.
                }

                // Modify the currently playing piano
                else
                    ChangePiano();
            }

            // If the destoyed balls are green
            if (ballColour == Image.value.green)
            {
                // If the strings aren't playing
                if (!stringCue1.IsPlaying && !stringCue2.IsPlaying && !stringCue3.IsPlaying && !stringCue4.IsPlaying)
                {
                    // If there's a string cue in memory, destroy it
                    if (stringCue1 != null)
                    {
                        disposeStringCues();
                        resetStringCues();
                    }

                    // Wait until the base melody has finished
                    while (!baseCue1.IsStopped && !baseCue2.IsStopped)
                    {
                        // TO DO
                    }
                    stringCue1.Play();                                                          // Play the piano now so that it is in sync.
                }

                // Modify the currently playing stringed instrument
                else
                    ChangeStrings();
            }

            // If the destoyed balls are red
            if (ballColour == Image.value.red)
            {
                // If the piano isn't playing
                if (!bellCue1.IsPlaying && !bellCue2.IsPlaying)
                {
                    // If there's a piano cue in memory, destroy it
                    if (bellCue1 != null)
                    {
                        disposeBellCues();
                        resetBellCues();
                    }

                    // Wait until the base melody has finished.
                    while (!baseCue1.IsStopped && !baseCue2.IsStopped)
                    {
                        // TO DO
                    }
                    bellCue1.Play();                                                           // Play the bell now so that it is in sync.
                }

                // Modify the currently playing piano
                else
                    ChangeBells();
            }
        }

        /// <summary>
        /// Updates the audio in the game.
        /// </summary>
        public void UpdateAudio()
        {
            musicEngine.Update();
        }

        /// <summary>
        /// Sets the position of the ball that caused an explosion.
        /// </summary>
        public void setPosition(Vector3 pos)
        {
            emitter.Position = pos;
        }
    }
}
