typedef struct my_struct
{
    int *f1;
    int *f2;
} my_struct_t;

my_struct_t struct_instance;

void main() {
    int a = 1;
    int b = 2;
    struct_instance.f1 = &a;
    struct_instance.f2 = &b;
}

//Should get that struct_instance.f1 points to a and struct_instance.f2 points to b