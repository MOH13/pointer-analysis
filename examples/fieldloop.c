typedef struct
{
    int *f1;
    int *f2;
} aggr;

int main()
{
    aggr a, *p;
    void *q;
    q = &a;
    p = q;
    q = &(p->f2);
}