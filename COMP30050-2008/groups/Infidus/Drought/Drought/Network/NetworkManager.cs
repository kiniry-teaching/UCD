using System;
using Microsoft.Xna.Framework.Net;
using System.Collections.Generic;

namespace Drought.Network
{
    /**
     * Manages network communication.
     */
    class NetworkManager
    {
        private static readonly int MAX_PLAYERS = 2;

        /** The session of the game we connected to. */
        private NetworkSession session;

        /** The single instance of this class. */
        private static NetworkManager instance = new NetworkManager();

        /** Used to format data for sending. */
        private PacketWriter packetWriter = new PacketWriter();

        /** Used to unpack data for receiving. */
        private PacketReader packetReader = new PacketReader();

        /** Internal constructor; user classes should obtain a reference through SoundManager.getInstance() */
        private NetworkManager() { }

        /* Returns the single instance of NetworkManager. */
        public static NetworkManager getInstance() {
            return instance;
        }

        /** Sends and recieves any pending packets. */
        public void update() {
            if (session != null) session.Update();
        }

        /** Host a subnet game. */
        public void host() 
        {
            session = NetworkSession.Create(NetworkSessionType.SystemLink, 1, MAX_PLAYERS, 0, null);
            session.GameStarted += new EventHandler<GameStartedEventArgs>(GameStarted);
            session.GameEnded += new EventHandler<GameEndedEventArgs>(GameEnded);
            session.SessionEnded += new EventHandler<NetworkSessionEndedEventArgs>(NetworkSessionEnded);
            session.GamerJoined += new EventHandler<GamerJoinedEventArgs>(GamerJoined);
            session.GamerLeft += new EventHandler<GamerLeftEventArgs>(GamerLeft);
            Console.WriteLine("Hosted Game");
        }

        /** Search the local subnet for joinable games, and return a list of RemoteGames representing them. */
        public List<RemoteGame> getLocalGames() 
        {
            AvailableNetworkSessionCollection sessions = NetworkSession.Find(NetworkSessionType.SystemLink, 1, null);
            Console.WriteLine("Found " + sessions.Count + " games");
            List<RemoteGame> remoteGames = new List<RemoteGame>();
            foreach (AvailableNetworkSession session in sessions) {
                if (session.CurrentGamerCount < MAX_PLAYERS) {
                    remoteGames.Add(new RemoteGame(session));
                }
            }
            return remoteGames;
        }

        /** Takes a RemoteGame and connects to it. */
        public void connectToGame(RemoteGame game)
        {
            session = NetworkSession.Join(game.getSession());
            session.GameStarted += new EventHandler<GameStartedEventArgs>(GameStarted);
            session.GameEnded += new EventHandler<GameEndedEventArgs>(GameEnded);
            session.SessionEnded += new EventHandler<NetworkSessionEndedEventArgs>(NetworkSessionEnded);
            session.GamerJoined += new EventHandler<GamerJoinedEventArgs>(GamerJoined);
            session.GamerLeft += new EventHandler<GamerLeftEventArgs>(GamerLeft);
            Console.WriteLine("Connected to game: " + game.getDescription());
        }

        private void GameStarted(object sender, GameStartedEventArgs args)
        {
            
        }
        
        private void GameEnded(object sender, GameEndedEventArgs args)
        {

        }
        
        private void NetworkSessionEnded(object sender, NetworkSessionEndedEventArgs args)
        {

        }

        private void GamerJoined(object sender, GamerJoinedEventArgs args)
        {

        }

        private void GamerLeft(object sender, GamerLeftEventArgs args)
        {

        }
    }
}
