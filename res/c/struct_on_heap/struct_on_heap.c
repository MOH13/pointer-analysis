// Test heap field-sensitivity

#include <stdlib.h>

typedef struct my_struct
{
    int *f1;
    int *f2;
} my_struct_t;

typedef struct my_struct2
{
    my_struct_t f1;
    int *f2;
} my_struct_t2;

int main()
{
    my_struct_t2 a, b;
    int x = 0;
    int y = 0;
    a.f1.f1 = &x;
    a.f2 = &y;
    my_struct_t2 *p = malloc(sizeof(my_struct_t2));
    *p = a;
    b = *p;
}
