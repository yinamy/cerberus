//CN_VIP #include <stdio.h>
#include <string.h>
#include <stdint.h>
#include <inttypes.h>
int y=2, x=1;
int main() {
  int *p = &x+1;
  int *q = &y;
  uintptr_t i = (uintptr_t)p;
  uintptr_t j = (uintptr_t)q;
  if (memcmp(&p, &q, sizeof(p)) == 0) {
    int *r = (int *)i;
    r=r-1;  // is this free of UB?
    *r=11;  // and this?
    //CN_VIP printf("x=%d y=%d *q=%d *r=%d\n",x,y,*q,*r);
    /*CN_VIP*//*@ assert (x == 11i32 && y == 2i32 && *q == 2i32 && *r == 11i32); @*/
  }
}