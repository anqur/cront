#include <stddef.h>
#include <stdint.h>
#include <assert.h>

static uint32_t
factorial_1(uint32_t n_2);

int
main(void);

static uint32_t
factorial_1(uint32_t n_2)
{
    uint32_t a_5;
    uint8_t exit_7;
    a_5 = 1;
    exit_7 = 0;
    do {
        if (n_2 > 1) {
            a_5 = a_5 * n_2;
            n_2 = n_2 - 1;
        } else {
            exit_7 = 1;
        }
    } while (!exit_7);
    return a_5;
}

int
main(void)
{
    uint32_t expr_8;
    uint32_t expr_9;
    expr_8 = factorial_1(10);
    expr_9 = expr_8 == 3628800;
    assert(expr_9);
    return 0;
}
