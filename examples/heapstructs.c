#include <stdlib.h>

typedef struct
{
    int *f1;
    int *f2;
} aggr;

int main()
{
    int x = 0;
    aggr *p = malloc(sizeof(aggr));
    p->f1 = p->f2 = &x;
    int *q = p->f2;
}