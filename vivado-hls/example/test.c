#include "test.h"

int *p;
int a, b;

__attribute__((noinline))
void f(){ p = &b; } 

int test () {
   a = 1; b = 2;
   p = &a;
   f();
   return (*p);
}

