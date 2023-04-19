int **a;

int main()
{
    int b = 2;
    int *c = &b;
    a = &c;

    int *d = *a;
}