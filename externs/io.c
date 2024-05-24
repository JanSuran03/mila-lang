#include <stdio.h>

void dec_int(int *x) {
    --(*x);
}

void read_int(int *x) {
    scanf("%d", x);
}

void write_int(int x) {
    printf("%d", x);
}

void write_str(const char *s) {
    printf("%s", s);
}

void writeln_int(int x) {
    printf("%d\n", x);
}

void writeln_str(const char *s) {
    printf("%s\n", s);
}
