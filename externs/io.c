#include <stdio.h>

void dec_int(int *x) {
    --(*x);
}

void inc_int(int *x) {
    ++(*x);
}

void read_int(int *x) {
    scanf("%d", x);
}

void read_float(float *x) {
    scanf("%f", x);
}

void write_int(int x) {
    printf("%d", x);
}

void write_float(float x) {
    printf("%f", x);
}

void write_str(const char *s) {
    printf("%s", s);
}

void writeln_int(int x) {
    printf("%d\n", x);
}

void writeln_float(float x) {
    printf("%f\n", x);
}

void writeln_str(const char *s) {
    printf("%s\n", s);
}

void swap_ints(int *x, int *y) {
    int tmp = *x;
    *x = *y;
    *y = tmp;
}

void swap_floats(float *x, float *y) {
    float tmp = *x;
    *x = *y;
    *y = tmp;
}
