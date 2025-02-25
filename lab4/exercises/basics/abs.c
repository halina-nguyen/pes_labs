#include <limits.h>

/*@
  requires INT_MIN <= x <= INT_MAX; 
  ensures (x >= 0 ==> \result == x) && (x < 0 ==> \result == -x);
  assigns \nothing; 
*/
int abs(int x)
{
    return (x < 0) ? -x : x;
}

int v;

void main(void)
{
    v = 10;
    int r1 = abs(-3);
    int r2 = abs(5);
    //@ assert r1 == 3;
    //@ assert r2 == 5;
    //@ assert v == 10;
}