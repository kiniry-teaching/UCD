package ie.ucd.music.comparison.Database;
public  class MusicItem {
    String artist;
    String song;
    int bitRate;
    String fileName;

       public void setMusicItem (String Aname, String Ttitle, int Brate, String fname) {

        artist = Aname;
        song = Ttitle;
        bitRate = Brate; 
        fileName = fname;

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

public String getfileName () {
    return fileName;

}
}