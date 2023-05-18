typedef struct my_struct
{
    int *f1;
    int *f2;
} my_struct_t;

int global_int = 5;
my_struct_t struct_instance[2] = {{.f1 = &global_int, .f2 = 0}, {.f1 = 0, .f2 = &global_int}};

int main()
{
    int a = 1;
    int b = 2;
    struct_instance[0].f1 = &a;
    struct_instance[0].f2 = &b;
}

// Should get that struct_instance.f1 points to a and struct_instance.f2 points to b
// Both f1 and f2 should point to global_int
