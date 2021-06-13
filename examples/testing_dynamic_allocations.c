#include <stdlib.h>

int main() {
    int* x = malloc(sizeof(int)*2);
    x[0] = 0;
    x[1] = 1;

    if (x[1] < 10) {
        x[0] = 4;
    } else {
        x[1] = 2;
    }
    return 0;
}