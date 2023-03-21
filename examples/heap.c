#include <stdlib.h>

int main()
{
    int x = 0;
    int **p = malloc(sizeof(int *));
    *p = &x;
    int *q = *p;
}