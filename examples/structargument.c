#include <stdlib.h>

typedef struct
{
    int *a;
    int b;
} st;

void foo(st c) {}

int main()
{
    st d;

    foo(d);

    return 0;
}