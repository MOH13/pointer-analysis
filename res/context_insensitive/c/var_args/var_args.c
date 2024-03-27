int x = 0;

int *var(int count, ...)
{
    return &x;
}

int main()
{
    int *p = var(1, 2);
}
