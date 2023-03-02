int a = 1;
int b = 2;
int c = 3;
int *gp = &c;

int main()
{
    int *p = &a;
    int *q = &b;
    p = q;
    p = gp;
}