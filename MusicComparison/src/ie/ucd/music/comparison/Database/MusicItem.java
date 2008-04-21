package ie.ucd.music.comparison.Database;
public  class MusicItem {
    String artist;
    String song;
    int bitRate;

       public void setMusicItem (String Aname, String Ttitle, int Brate) {

        artist = Aname;
        song = Ttitle;
        bitRate = Brate; 

    }
    public String getArtist () {
        return artist;

    }
    public String getSong () {
        return song;

    }
    public int getBitRate () {
        return bitRate;

    }
}