#include <stdio.h>
#include <stdint.h>
#include <assert.h>

extern uint64_t __addm(uint64_t, uint64_t, uint64_t);
extern uint64_t __subm(uint64_t, uint64_t, uint64_t);
extern uint64_t __mulm(uint64_t, uint64_t, uint64_t);

uint64_t tadd[][4] =
 { { 18446744073709551557ull , 18446744073709551554ull , 18446744073709551552ull , 18446744073709551549ull }
 , { 18446744073709551557ull , 18446744073709551554ull , 50ull , 47ull }
 , { 18446744073709551557ull , 62ull , 50ull , 112ull }
 , { 2, 0, 0, 0 }
 , { 2, 0, 1, 1 }
 , { 2, 1, 0, 1 }
 , { 2, 1, 1, 0 }
 };

uint64_t tsub[][4] =
 { { 18446744073709551557ull , 50ull , 62ull , 18446744073709551545ull }
 , { 18446744073709551557ull , 18446744073709551556ull , 18446744073709551554ull , 2ull }
 , { 18446744073709551557ull , 60ull , 18446744073709551554ull , 63ull }
 , { 2, 0, 0, 0 }
 , { 2, 0, 1, 1 }
 , { 2, 1, 0, 1 }
 , { 2, 1, 1, 0 }
 };

uint64_t tmul[][4] =
 { { 18446744073709551557ull , 60ull , 18446744073709551554ull , 18446744073709551377ull }
 , { 18446744073709551557ull , 60ull , 62ull , 3720ull }
 , { 18446744073709551557ull , 18446744073709551556ull , 18446744073709551554ull , 3ull }
 , { 2, 0, 0, 0 }
 , { 2, 0, 1, 0 }
 , { 2, 1, 0, 0 }
 , { 2, 1, 1, 1 }
 };

int main() {
  int i, b, r;
  printf("Testing ADDM: ");
  b = 1;
  for (i=0; i<sizeof(tadd)/32; i++) {
    r = __addm(tadd[i][0], tadd[i][1], tadd[i][2]);
    assert (r == tadd[i][3]);
    b = b && (r == tadd[i][3]);
  }
  if (b) printf("OK\n"); else printf("FAIL!\n");

  printf("Testing SUBM: ");
  b = 1;
  for (i=0; i<sizeof(tadd)/32; i++) {
    r = __subm(tsub[i][0], tsub[i][1], tsub[i][2]);
    assert (r == tsub[i][3]);
    b = b && (r == tsub[i][3]);
  }
  if (b) printf("OK\n"); else printf("FAIL!\n");

  printf("Testing MULM: ");
  b = 1;
  for (i=0; i<sizeof(tadd)/32; i++) {
    r = __mulm(tmul[i][0], tmul[i][1], tmul[i][2]);
    assert (r == tmul[i][3]);
    b = b && (r == tmul[i][3]);
  }
  if (b) printf("OK\n"); else printf("FAIL!\n");

  return 0;
}

