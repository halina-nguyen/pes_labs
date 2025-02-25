/*@
    requires \valid(x) && \valid_read(y);
    requires \separated(x, y);
    ensures *x == \old(*x) - *y;
    ensures *y == \old(*y); 
*/
void decr_by(int* x, int const* y)
{
    *x = *x - *y;
}

void main(void)
{
    int x = 7;
    int y = 3;
    decr_by(&x, &y);
    //@ assert x == 4;
    //@ assert y == 3;
}
