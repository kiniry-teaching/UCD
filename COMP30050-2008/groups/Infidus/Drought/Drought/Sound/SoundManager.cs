using System;
using System.Collections.Generic;
using Microsoft.Xna.Framework;
using Microsoft.Xna.Framework.Audio;
using Drought.Entity;
using Drought.World;

namespace Drought.Sound
{
    /** Provides unique handles for the various sounds in the game, to avoid passing around unsafe strings. */
    public enum SoundHandle : int { Truck }

    /**
     * Provides methods to play sounds.
     */
    class SoundManager
    {
        /* XNA sound components */
        private AudioEngine audioengine;
        private SoundBank soundBank;
        private WaveBank waveBank;

        /* The single instance of SoundManger. */
        private static SoundManager instance = new SoundManager();

        /* Where the sound is played "to". */
        private AudioListener listener;
        private Camera listenerCamera;

        /** Cues */
        List<Sound> soundList = new List<Sound>();
        
        /** Whether sound is playing at the moment. */
        private bool soundOn;

        /** Internal constructor; user classes should obtain a reference through SoundManager.getInstance() */
        private SoundManager()
        {
            audioengine = new AudioEngine("Content/Audio/Win.xgs");
            soundBank = new SoundBank(audioengine, "Content/Audio/Win Sound Bank.xsb");
            waveBank = new WaveBank(audioengine, "Content/Audio/Win Wave Bank.xwb");
            //playSound(SoundHandle.BGM);
            listener = new AudioListener();
            soundOn = true;
        }

        /** Returns the one instance of SoundManager.  */
        public static SoundManager getInstance()
        {
            return instance;
        }

        /** Sets the sound listener. */
        public void setListener(Camera theListener)
        {
            listenerCamera = theListener;
        }

        public void update()
        {
            if (listenerCamera != null) {
                listener.Position = listenerCamera.getPosition();
            }
            foreach (Sound sound in soundList) {
                sound.getCue().Apply3D(listener, sound.getEmitter(listenerCamera));
            }
            audioengine.Update();
        }

        /** Turns the sound on or off. */
        public void toggleSound()
        {
            soundOn = !soundOn;
        }

        /* Plays a sound at its default volume, not positioned in 3D space. */
        public void playSound(SoundHandle theSound)
        {
            if (soundOn) {
                switch (theSound) {
                    case SoundHandle.Truck: soundBank.PlayCue("truck"); break;
                    //case SoundHandle.Punch: soundBank.PlayCue("punch"); break;
                    //case SoundHandle.BGM: soundBank.PlayCue("bgm"); break;
                }
            }
        }

        /* Plays a sound positioned in 3D space, with panning and volume adjustments. */
        public void playSound(SoundHandle theSound, MovableEntity emitterEntity)
        {
            if (soundOn) {
                if (emitterEntity == null) playSound(theSound); //if the listener isn't set, just play the sound normally
                AudioEmitter emitter = new AudioEmitter();
                emitter.Position = emitterEntity.getPosition();
                switch (theSound) {
                    case SoundHandle.Truck:
                        Cue newCue = soundBank.GetCue("truck");
                        Sound newSound = new Sound(newCue, emitterEntity);
                        newCue.Apply3D(listener, emitter);
                        newCue.Play();
                        soundList.Add(newSound); 
                        break;
                    //case SoundHandle.Punch: soundBank.PlayCue("punch", listener, emitter); break;
                    //case SoundHandle.BGM: soundBank.PlayCue("bgm"); break;
                }
            }
        }
    }

    class Sound
    {
        private Cue cue;

        private MovableEntity entity;

        private AudioEmitter emitter;

        public Sound(Cue theCue, MovableEntity emitterEntity)
        {
            cue = theCue;
            entity = emitterEntity;
            emitter = new AudioEmitter();
        }

        public Cue getCue()
        {
            return cue;
        }

        public AudioEmitter getEmitter(Camera listenerCamera)
        {
            Vector3 relativePos = entity.getPosition() -listenerCamera.getPosition();

            Matrix rotation = Matrix.CreateRotationZ(-listenerCamera.getOrientation());
            Matrix translation = Matrix.CreateTranslation(listenerCamera.getPosition());

            Vector3 newPos = Vector3.Transform(relativePos, rotation * translation);
            
            emitter.Position = newPos;
            return emitter;
        }
    }
}
