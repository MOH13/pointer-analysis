int x = 0;

int *var()
{
    return &x;
}

int main()
{
    int *p = var(0);
}
