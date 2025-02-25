/*@
    requires 0 <= len;
    requires \valid(arr + (0 .. len-1));
    ensures \forall int i; 0 <= i < len ==> \result <= arr[i];
    ensures \exists int i; 0 <= i < len && arr[i] == \result;
*/
int find_min(int* arr, int len)
{
    int min = arr[0];
    /*@
        loop invariant 0 <= i <= len;
        loop invariant \forall int j; 0 <= j < i ==> min <= arr[j];
        loop invariant \exists integer k; 0 <= k < i && min == arr[k];
        loop assigns i, min;
        loop variant len - i;
    */
    for (int i = 1; i < len; i++)
        if (arr[i] < min)
            min = arr[i];

    return min;
}

void main(void)
{
    int a[] = {3, 5, 18, 2, 12};
    int r = find_min(a, 5);
    //@ assert r == 2;
}