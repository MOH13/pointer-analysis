#include <stdarg.h>

int *var(int *p, ...)
{
    va_list ap;
    va_start(ap, p);
    int *out = va_arg(ap, int *);
    out = va_arg(ap, int *);
    va_end(ap);
    return out;
}

int main()
{
    int x, y, z;
    int *q = var(&x, &y, &z);
}
