/*@ 
  requires \valid(a) && \valid(b);
  requires \separated(a, b);
  ensures \result == *a + *b;
*/
int add_ptr(int* a, int* b)
{
    return *a + *b;
}

void main(void)
{
    int a = 13;
    int b = 15;
    int r = add_ptr(&a, &b);
    //@ assert r == 28;
}