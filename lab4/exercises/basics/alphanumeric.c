int is_alphanumeric(char c)
{

}

void main()
{
    int r;

    r = is_alphanumeric('0');
    //@ assert r;

    r = is_alphanumeric('x');
    //@ assert r;

    r = is_alphanumeric(' ');
    //@ assert !r;
}
