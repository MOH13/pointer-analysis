// Simple test with struct assignment

typedef struct my_struct
{
    int *f1;
    int *f2;
} my_struct_t;

my_struct_t struct_instance;

int main()
{
    my_struct_t a, b;
    int c = 0;
    a.f2 = &c;
    b = a;
}