// Tests array insensitivity and nested structs

typedef struct
{
    int *f;
    int *g;
} simple;

int main()
{
    int a = 0;
    int b = 0;
    int c = 0;
    int d = 0;

    simple x[] = {{.f = &a, .g = &b}, {.f = &c, .g = &d}};
}