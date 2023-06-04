typedef struct
{
    int f;
    int g;
} st;

int main()
{
    st a;
    int *p = ((int *)&a) + 1;
}