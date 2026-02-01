#include <stddef.h>
#include <stdint.h>
#include <assert.h>

static uint32_t
id_10(uint32_t a_3);

static uint64_t
add_11(uint64_t a_6, uint64_t b_7);
static double
add_12(double a_6, double b_7);

int
main(void);

static uint32_t
id_10(uint32_t a_3)
{
    return a_3;
}

static uint64_t
add_11(uint64_t a_6, uint64_t b_7)
{
    return a_6 + b_7;
}
static double
add_12(double a_6, double b_7)
{
    return a_6 + b_7;
}

int
main(void)
{
    uint32_t expr_13;
    uint32_t expr_14;
    uint32_t expr_15;
    uint32_t expr_16;
    uint64_t expr_17;
    uint64_t expr_18;
    double expr_19;
    double expr_20;
    expr_13 = id_10(1);
    expr_14 = expr_13 == 1;
    assert(expr_14);
    expr_15 = id_10(2);
    expr_16 = expr_15 == 2;
    assert(expr_16);
    expr_17 = add_11(1, 1);
    expr_18 = expr_17 == 2;
    assert(expr_18);
    expr_19 = add_12(1, 1);
    expr_20 = expr_19 == 2;
    assert(expr_20);
    return 0;
}
