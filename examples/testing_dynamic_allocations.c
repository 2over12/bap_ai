#include <stdlib.h>

int main() {
    int* x = malloc(sizeof(int)*2);
    x[0] = 0;
    x[1] = 1;
    return 0;
}