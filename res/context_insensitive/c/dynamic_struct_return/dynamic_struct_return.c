#include <stdlib.h>

typedef struct
{
    int f1;
    int *f2;
} st;

int x = 0;
int y = 1;

st a()
{
    st ret = {.f1 = 2, .f2 = &x};
    return ret;
}

st b()
{
    st ret = {.f1 = 3, .f2 = &y};
    return ret;
}

int main()
{
    st (*f)() = rand() ? a : b;
    int *p = f().f2;
}