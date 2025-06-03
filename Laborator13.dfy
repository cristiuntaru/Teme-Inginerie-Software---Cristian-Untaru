//Exercițiul 1 b)
method Max(x: int, y: int) returns (m: int)
  ensures m == if x >= y then x else y
{
  if x >= y {
    m := x;
  } else {
    m := y;
  }
}

method MaxSum(x: int, y: int) returns (s: int, m: int)
  ensures s == x + y
  ensures m == if x >= y then x else y
{
  s := x + y;
  m := Max(x, y);
}



//Exercițiul 1 c)
method TestMaxSum()
{
  var s, m := MaxSum(1928, 1);
  print "Suma: ", s, "\n";
  print "Maximul: ", m, "\n";
}


//Exercițiul 2 a)
method ReconstructFromMaxSum(s: int, m: int) returns (x: int, y: int)
  requires s <= 2 * m
  ensures s == x + y
  ensures (m == x || m == y) && x <= m && y <= m
{
  x := m;
  y := s - m;
}

//Exercițiul 2 b)
method TestMaxSum2(x: int, y: int)
{
  var s, m := MaxSum(x, y);
  assume m <= s <= 2 * m;
  var xx, yy := ReconstructFromMaxSum(s, m);
  assert (xx == x && yy == y) || (xx == y && yy == x);
}
