// Test heap cells

#include <stdlib.h>

typedef struct
{
    int a;
} st;

int main()
{
    int *ints = malloc(sizeof(int) * 10);
    int *i = &ints[4];
    st *structs = malloc(sizeof(st) * 10);
    st *s = &structs[4];
}