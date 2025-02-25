#include <limits.h>

/*@
  requires INT_MIN <= x <= INT_MAX; 
  ensures \result == ((x > y) ? x : y);
*/
int max(int x, int y)
{
    return (x > y) ? x : y;
}

int main(void)
{
    int r1 = max(3, 5);
    int r2 = max(6, 2);
    int r3 = max(4, 4);
    //@ assert r1 == 5;
    //@ assert r2 == 6;
    //@ assert r3 == 4;
}