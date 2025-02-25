/*@
    requires 0 <= len;
    requires \valid(arr + (0 .. len-1));
    assigns arr[0 .. len-1];
    ensures \forall int i; 0 <= i < len ==> arr[i] == start + i;
*/
void linrange(int* arr, int len, int start) 
{
    /*@
        loop invariant 0 <= i <= len;
        loop invariant \forall int j; 0 <= j < i ==> arr[j] == start + j;
    */
    for (int i = 0; i < len; i++)
        arr[i] = start + i;
}

int main(void) 
{
    int a[5];
    linrange(a, 5, 2);

    //@ assert a[0] == 2;
    //@ assert a[1] == 3;
    //@ assert a[2] == 4;
    //@ assert a[3] == 5;
    //@ assert a[4] == 6;

    return 0;
}