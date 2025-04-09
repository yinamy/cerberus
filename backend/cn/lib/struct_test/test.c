#include "./headers.h" 

void do_nothing (struct point p) 
/*@ requires true;
  ensures p.x == p.x;
@*/
{
  /*@ apply struct_lemma (p); @*/
  p.x = p.x;
}

int read (int *p)
/*@ requires 
      take P = Owned<int>(p);
      (i32) P == 0i32;
  ensures 
      take Q = Owned<int>(p);
      (i32) Q == 0i32;
@*/
{
  /*@ apply resource_lemma (p); @*/
  return *p;
}