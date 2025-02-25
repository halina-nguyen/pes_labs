/*@ 
  requires 1 <= month <= 12;
  ensures \result \in {28, 30, 31};
*/
int number_of_days(int month){
  int days[] = { 31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31 };
  return days[month-1];
}

int main(void)
{
    int r1 = number_of_days(2);
    int r2 = number_of_days(6);
    int r3 = number_of_days(12);
    //@ assert r1 == 28;
    //@ assert r2 == 30;
    //@ assert r3 == 31;

    return 0;
}