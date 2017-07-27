#include "iRRAM/lib.h"

using namespace iRRAM;

int REAL_lt(int n, REAL a, REAL b) {
  REAL err = power(2, n);
  return 2 - choose(a < b + err, b < a + err);
}
