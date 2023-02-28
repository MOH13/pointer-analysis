int main() {
    int* null_p = 0;
    int** pp = &null_p;
    int* q = (int*) pp;
    *pp = q;
}