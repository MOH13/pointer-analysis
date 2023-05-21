int main()
{
    int a = 0;
    int* p = &a;
    int** q = &p;

    while (1) {
        int** r = q;
        int b = 0;
        *r = &b;
        q = r;
    }
}