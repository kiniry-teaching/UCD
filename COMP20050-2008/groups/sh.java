public class sh
{

public static void main(String[] args)
{
int i = 2048;
int r =0;
while(true)
{
r++;
i = i * 2;
if(i==16384000)
{
System.out.println("aya " + r);
break;
}

System.out.println(i);
wait(100);
}

}
}
