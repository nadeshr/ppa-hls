#include "test.h"
 
int main () {
   int retval = 0;
   int result = test();
   if(result!=2) retval = 1;
   return retval;
}
