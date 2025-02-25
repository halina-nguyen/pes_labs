#include <stddef.h>

/*@
    requires 0 <= n;
    requires \valid(a + (0..n-1));
    requires \valid(b + (0..n-1));
    ensures 0 <= \result <= n;
    ensures \result == n || a[\result] != b[\result];
    ensures \forall integer i; 0 <= i < \result ==> a[i] == b[i];
*/
int mismatch(int* a, int* b, int n) {
    /*@
        loop invariant 0 <= i <= n;
        loop invariant \forall int j; 0 <= j < i ==> a[i] == b[i];
    */
    for (int i = 0; i < n; i++)
        if (a[i] != b[i])
            return i;

    return n;
}

int main() {
    int x[] = {1, 2, 3, 4, 5};
    int y[] = {1, 2, 0, 4, 5};
    int z[] = {1, 2, 3, 4, 5};

    int r1 = mismatch(x, y, 5);
    int r2 = mismatch(x, z, 5);

    //@ assert r1 == 2;
    //@ assert r2 == 5;
}