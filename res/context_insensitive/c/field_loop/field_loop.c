// Has a dependency loop between p and q with an offset edge

typedef struct
{
    int *f1;
    int *f2;
} aggr;

int main()
{
    aggr a, *p;
    void *q = &a;
    p = q;
    q = &(p->f2);
}