// Tests multiple functions and flow through function calls

int* id(int* p) {
    int x = 2;
    return p;
}

int main() {
    int x = 1;
    int* p = &x;
    int* q = id(p);
}