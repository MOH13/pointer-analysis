typedef struct
{
    int *a;
    int b;
} st;

st foo(st c) { return c; }

int main()
{
    st d;
    int e;
    d.a = &e;

    st f = foo(d);
}