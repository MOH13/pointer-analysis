#include <stdlib.h>

int main() {
    int x = 0;
    int y = 42;
    int* p;
    if (rand()) {
        p = &x;
    } else {
        p = &y;
    }
}