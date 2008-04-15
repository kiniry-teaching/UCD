using System;
using System.Collections.Generic;
using System.Text;
using Microsoft.Xna.Framework.Net;

namespace Drought.Network 
{

    /**
     * Represents a joinable game.
     */
    class RemoteGame 
    {
        private AvailableNetworkSession session;

        public RemoteGame(AvailableNetworkSession aSession)
        {
            session = aSession;
        }

        public String getDescription()
        {
            return session.HostGamertag;
        }

        public AvailableNetworkSession getSession()
        {
            return session;
        }
    }
}
