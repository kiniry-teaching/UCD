#include 

template inline T SQR( T x ){ return x*x; };

int main()
{
    double a = 1.123456789012345678;
    float b = float( a );

    cout << "double SQR = " << SQR( a ) << '\n'
         << "float  SQR = " << SQR( b ) << '\n';
}
