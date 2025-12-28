
void printf(char* format, ...);

int main(void) {

    printf("Hello World! %d %f\n", 420, 67.69);
    printf("ints: %d %d %d %d %d %d %d %d\n", 1, 2, 3, 4, 5, 6, 7, 8);
    printf("doubles: %.1f %.1f %.1f %.1f\n", 1.0, 2.0, 3.0, 4.0);
    printf("fixed+var: %.1f %.1f %.1f\n", 10.0, 20.0, 30.0);

    printf("fp overflow: %.0f %.0f %.0f %.0f %.0f %.0f %.0f %.0f %.0f %.0f\n",
           1.0, 2.0, 3.0, 4.0, 5.0,
           6.0, 7.0, 8.0, 9.0, 10.0);

    printf(
        "sat: %d %d %d %d %d %d %d %d "
        "%.0f %.0f %.0f %.0f %.0f %.0f %.0f %.0f %.0f %.0f\n",
        /* GP args (8 total → 6 regs + 2 stack) */
        1, 2, 3, 4, 5, 6, 7, 8,
        /* FP args (10 total → 8 regs + 2 stack) */
        1.0, 2.0, 3.0, 4.0, 5.0,
        6.0, 7.0, 8.0, 9.0, 10.0
    );

    printf(
        "zigzag: %d %.0f %d %.0f %d %.0f %d %.0f "
        "%d %.0f %d %.0f\n",
        1,  1.0,
        2,  2.0,
        3,  3.0,
        4,  4.0,
        5,  5.0,
        6,  6.0
    );

    printf(
        "align: %d %.1f %d %.1f %d %.1f %d %.1f\n",
        1, 1.1,
        2, 2.2,
        3, 3.3,
        4, 4.4
    );

    return 0;
}
