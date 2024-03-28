// Cast between one-field struct and int pointer
// + struct assignment

int x;

int *id(int *a) {
    return a;
}

int main()
{
    int *y = id(&x);
}