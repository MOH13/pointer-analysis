// Test heap field-sensitivity

#include <stdlib.h>

typedef struct my_struct
{
    int *f1;
    int *f2;
} my_struct_t;

int main()
{
    my_struct_t a, b;
    int x = 0;
    int y = 0;
    a.f1 = &x;
    a.f2 = &y;
    my_struct_t *p = malloc(sizeof(my_struct_t));
    *p = a;
    b = *p;
}
