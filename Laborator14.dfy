// Exercițiul 1

// 1. Suma primelor n numere naturale
method Sum(n: nat) returns (s: nat)
  ensures s == n * (n + 1) / 2
{
  s := 0;
  var i := 0;
  while i <= n
    invariant 0 <= i <= n + 1
    invariant s == i * (i - 1) / 2
    decreases n - i + 1
  {
    s := s + i;
    i := i + 1;
  }
}


// 2. Verificare numar prim
method IsPrime(n: nat) returns (result: bool)
  requires n >= 2
  ensures result ==> (forall d: nat :: 2 <= d < n ==> n % d != 0)
{
  var d := 2;
  result := true;

  while d < n && result
    invariant 2 <= d <= n
    invariant result ==> (forall k: nat :: 2 <= k < d ==> n % k != 0)
    decreases n - d
  {
    if n % d == 0 {
      result := false;
    }
    d := d + 1;
  }
}


// 3. Verificare numar perfect
method IsPerfect(n: nat) returns (result: bool)
  requires n >= 2
  ensures result ==> (forall d: nat :: 1 <= d < n && n % d == 0 ==> d <= n)
{
  var sum := 0;
  var d := 1;
  result := false;

  while d < n
    invariant 1 <= d <= n
    decreases n - d
  {
    if n % d == 0 {
      sum := sum + d;
    }
    d := d + 1;
  }

  if sum == n {
    result := true;
  }
}





// Exercițiul 2

//a
function F(x: int): int
  decreases x
{
  if x < 10 then x else F(x - 1)
}


//b
function G(x: int): int
  decreases x
{
  if 0 <= x then G(x - 2) else x
}


//c
function H(x: int): int
  decreases x + 61
{
  if x < -60 then x else H(x - 1)
}


//d
function I(x: nat, y: nat): int
  decreases x + y
{
  if x == 0 || y == 0 then 12
  else if x % 2 == y % 2 then
    I(x - 1, y)
  else
    I(x, y - 1)
}


//e
function J(x: nat, y: nat): int
  decreases x, y
{
  if x == 0 then y
  else if y == 0 then
    J(x - 1, 3)
  else
    J(x, y - 1)
}


//f
function K(x: nat, y: nat, z: nat): int
  decreases x, y, z
{
  if x < 10 || y < 5 then x + y
  else if z == 0 then
    K(x - 1, y, 5)
  else
    K(x, y - 1, z - 1)
}


//g
function L(x: int): int
  decreases 100 - x
{
  if x < 100 then L(x + 1) + 10 else x
}


