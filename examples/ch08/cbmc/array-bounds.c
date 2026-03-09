#include <assert.h>

extern int nondet_int(void);

int main(void) {
  int array[10];
  int index = nondet_int();

  __CPROVER_assume(index >= 0 && index < 10);
  array[index] = 42;

  int x = nondet_int();
  int y = nondet_int();
  __CPROVER_assume(x >= 0 && x <= 1000);
  __CPROVER_assume(y >= 0 && y <= 1000);

  int sum = x + y;
  __CPROVER_assert(sum >= x && sum >= y, "sum grows for bounded non-negative inputs");
  return 0;
}
