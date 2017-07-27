#include <iostream>
#include "iRRAM/lib.h"

using namespace iRRAM;

int ilog2(REAL);

int iRRAM_compute(const int& dummy) {
  double x;

  std::cout << "ilog2()\n";
  std::cin >> x;

  std::cout << "ilog2(" << x << ") = " << ilog2(REAL(x)) << std::endl;

  return 0;
}

int main (int argc,char **argv)
{
  iRRAM_initialize(argc,argv);
  return iRRAM_exec(iRRAM_compute, 0);
}
