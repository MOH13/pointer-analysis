// Tests multiple functions and flow through function calls

int *id(int *param)
{
    int x = 2;
    return param;
}

int main()
{
    int x = 1;
    int *p = &x;
    int *q = id(p);
}
