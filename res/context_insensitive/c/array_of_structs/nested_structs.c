// Tests array insensitivity and nested structs

typedef struct
{
    int *field;
} simple;

typedef struct
{
    struct
    {
        int f11;
        int f12;
    } f1;
    struct
    {
        int *f21;
        simple f22;
    } f2[10];
} nested;

int main()
{
    int x = 0;
    nested a;
    a.f2[7].f21 = &x;

    nested *ap = &a;
    ap->f2[7].f22.field = ap->f2[7].f21;
    int *q = ap->f2[7].f22.field;
}