int *id(int *p)
{
    return p;
}

int main()
{
    int x;
    int *(*f)(int *) = id;
    int *q = f(&x);
}