// Test global struct initializers

typedef struct
{
    int *f1;
    int *f2;
} st;

int x = 4;
int y = 5;

int main()
{
    int local = 0;
    st a = {.f1 = &x, .f2 = &local};
    st b = {.f1 = &y, .f2 = &x};
    a = b;
    return 0;
}