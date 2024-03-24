int *id(int *x)
{
    return x;
}

int main()
{
    int a = 0;
    int b = 0;
    int *ap = id(&a);
    int *bp = id(&b);
    return 0;
}