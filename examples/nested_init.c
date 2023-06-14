#include <stdlib.h>

int x = 0;
int y = 1;

typedef struct
{
    int *f;
    int *g;
} other;

typedef union
{
    int *q;
    other b;
} union_t;

struct
{
    int *f0;
    union_t f2;
} global[2] = {{.f0 = &x, .f2 = {.q = &y}}, {.f0 = &y, .f2 = {.b = {&x, &y}}}};

int main()
{
    union_t h = global[rand() % 2].f2;
}