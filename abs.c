int abs (int x)
/*@ requires let X = (i64) x;
            (i64)MINi32() <= X; X <= (i64)MAXi32();
            (i64)MINi32() <= -X; -X <= (i64)MAXi32();
ensures return == ((x >= 0i32) ? x : -x);
@*/

{
  if (x >= 0) {
    return x;
  } else {
    return -x;
  }
}
