/*@
predicate (datatype List) Array (pointer p, i32 n) {
  if (n == 0i32) {
    return Nil{};
  } else {
    take V = Owned<int>(p);
    take VS = Array(array_shift<int>(p, 1), n-1i32);
    return (Cons { Head: V, Tail: VS });
  }
}
@*/