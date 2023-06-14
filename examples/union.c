typedef union
{
    int *ptr;
    int num;
} ut;

int x = 0;
static ut global[2] = {{.ptr = &x}, {.num = 4}};

int main()
{
    int *p = global[0].ptr;
}