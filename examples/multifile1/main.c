#include "other.h"

int main() {
    int x = 2;
    int *y = foo(&x);
    return *y;
}