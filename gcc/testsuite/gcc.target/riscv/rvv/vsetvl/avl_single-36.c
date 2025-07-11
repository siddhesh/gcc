/* { dg-do compile } */
/* { dg-options "-mrvv-vector-bits=scalable -march=rv32gcv -mabi=ilp32 -fno-schedule-insns -fno-schedule-insns2 -fno-tree-vectorize" } */

#include "riscv_vector.h"

void f (int8_t * restrict in, int8_t * restrict out, int n, int cond)
{
  for (size_t i = 0; i < n; i++)
    {
      vint8mf8_t v = __riscv_vle8_v_i8mf8 (in + i + 300,555 + cond);
      __riscv_vse8_v_i8mf8 (out + i + 300, v,555 + cond);
    }

  for (size_t i = 0; i < n; i++)
    {
      vint8mf8_t v = __riscv_vle8_v_i8mf8 (in + i,555 + cond);
      __riscv_vse8_v_i8mf8 (out + i, v,555 + cond);
      
      vint8mf8_t v2 = __riscv_vle8_v_i8mf8_tu (v, in + i + 100,555 + cond);
      __riscv_vse8_v_i8mf8 (out + i + 100, v2,555 + cond);
    }
}

/* { dg-final { scan-assembler-times {vsetvli\s+zero,\s*[a-x0-9]+,\s*e8,\s*mf8,\s*tu,\s*m[au]} 1 { target { no-opts "-O0" no-opts "-g" no-opts "-funroll-loops" } } } } */
/* { dg-final { scan-assembler-times {vsetvli} 1 { target { no-opts "-O0" no-opts "-Os" no-opts "-g" no-opts "-funroll-loops" no-opts "-Oz" } } } } */
