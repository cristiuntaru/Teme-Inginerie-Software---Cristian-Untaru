method Between(p: int, r: int) returns (q: int)
  requires r - p > 1
  ensures p < q < r
{
  q := p + 1;
}
