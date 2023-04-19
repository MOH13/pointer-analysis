// Simple test of field sensitivity

#include <stdio.h>

typedef struct my_struct
{
    int *f1;
    int f2;
} my_struct_t;

int main()
{
    my_struct_t a;
    my_struct_t *p = &a;
    int x = 1;
    p->f1 = &x;
    int *q = &p->f2;
}