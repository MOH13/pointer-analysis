int *foo(int *p)
{
    static int *q = 0;
    q = p;
    return q;
}

int main()
{
    int x = 0;
    int *r = foo(&x);
}
