// Options:   --no-argc --no-arrays --no-bitfields --checksum --concise --no-consts --no-float --no-inline-function --max-array-dim 3 --max-array-len-per-dim 10 --max-block-depth 5 --max-block-size 4 --max-expr-complexity 2 --max-funcs 1 --max-pointer-depth 2 --no-pointers --no-structs --no-unions --no-volatiles --no-builtins -o small_int_arith/csmith_024.c
#include "csmith.h"


static long __undefined;



static uint32_t g_6 = 0xA0E60F95L;
static int32_t g_9 = 0x6B471DFDL;



static int64_t  func_1(void);




static int64_t  func_1(void)
{ 
    uint16_t l_7 = 0x210EL;
    int32_t l_8 = 0x9729CF30L;
    int32_t l_10 = (-4L);
    g_9 = (safe_mul_func_int8_t_s_s((safe_lshift_func_uint8_t_u_u((g_6 >= 0x77DD68876942A1E9LL), l_7)), l_8));
    l_10 = g_6;
    return l_7;
}





int main (void)
{
    int print_hash_value = 0;
    platform_main_begin();
    crc32_gentab();
    func_1();
    transparent_crc(g_6, "g_6", print_hash_value);
    transparent_crc(g_9, "g_9", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
