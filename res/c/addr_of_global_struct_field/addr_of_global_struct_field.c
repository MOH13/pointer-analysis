#include <stdlib.h>

typedef struct
{
    int *a;
    int f;
} st;

st b;

int main()
{
    int* c = &b.f; 
    return 0;
}