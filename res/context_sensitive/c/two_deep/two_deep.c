int *id1(int *x)
{
    return x;
}

int *id2(int *x)
{
    return id1(x);
}

int main()
{
    int a = 0;
    int b = 0;
    int *ap = id2(&a);
    int *bp = id2(&b);
    return 0;
}