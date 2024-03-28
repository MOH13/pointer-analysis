// Cast between one-field struct and int pointer
// + struct assignment

int x;
int *y = &x;

int *id(int *a) {
    return a;
}

int main()
{
    int *z = id(y);
}