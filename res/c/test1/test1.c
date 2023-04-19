int main()
{
    int y = 0;
    int *x = &y;
    int *z = x;
    *z = y;
    return 0;
}