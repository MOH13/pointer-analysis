typedef struct
{
    int *ptr;
} st;

int main()
{
    int x = 0;
    int *p = &x;
    st a, b;
    st *stp = (st *)&p;
    b = *stp;
    a = b;
}