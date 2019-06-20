#include <klee/klee.h>

int get_sign(int x) {
  if (x == 0)
     return 0;
  
  if (x < 0)
     return -1;
  else 
     return 1;
} 

int main() {
  int a = 5;
  //klee_make_symbolic(&a, sizeof(a), "a");
  
  int res = 0;
  while(res < 5) {
  	res += get_sign(a);
  }
  
  return res;
} 

