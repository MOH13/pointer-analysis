#include <stdlib.h>

int main()
{
    int *xs = malloc(sizeof(int) * 4);
    int i = 2;
    int *p = xs + i;
}