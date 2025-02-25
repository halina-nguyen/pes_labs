/*@
    requires 0 <= len;
    requires \valid(arr + (0 .. len-1));
    ensures \forall int i; 0 <= i < len-1 ==> arr[i] <= arr[i+1];
*/
int is_sorted(int* arr, int len) 
{
    /*@
        loop invariant 0 <= i <= len;
        loop invariant \forall int j; 0 <= j < i ==> arr[i] <= arr[i+1];
    */
    for (int i = 1; i < len; i++)
        if (arr[i] < arr[i - 1])
            return 0;

    return 1;
}

int main()
{
    int a1[] = {1,2,3};
    int a2[] = {2,1,3}; 

    int r1 = is_sorted(a1, 3); 
    int r2 = is_sorted(a2, 3); 

    //@ assert r1 == 1;
    //@ assert r2 == 0; 
}
