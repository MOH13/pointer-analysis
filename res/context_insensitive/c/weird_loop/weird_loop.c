// #include <stdio.h>

typedef struct {
    int* f0;
    int* f1;
    int* f2;
} S;

typedef struct {
    int* f0;
    int* f1;
} S2;

int main() {
    S a;
    void *b = (void *)&a;
    S2* c = (S2 *) b;
    int **d = &c->f1;
    b = (void *)d;
    int e;
    int **f = (int **)c;
    *f = &e;

    // printf("a.f0 == &e: %d\n", a.f0 == &e);

    c = (S2 *) b;
    d = &c->f1;
    b = (void *)d;

    f = (int **)c;
    *f = &e;

    // printf("a.f1 == &e: %d\n", a.f1 == &e);
}