// Cast between one-field struct and int pointer
// + struct assignment

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