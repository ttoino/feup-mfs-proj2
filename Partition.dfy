method Partition(a: array<int>, s: nat, l: nat, x: int)
  returns (m: nat, n: nat)
  modifies a
  requires 0 <= s < l
  requires 1 <= l <= a.Length
  ensures s <= m <= n <= l
  ensures forall i :: 0 <= i < s ==> a[i] == old(a[i])
  ensures forall i :: s <= i < m ==> a[i] < x
  ensures forall i :: m <= i < n ==> a[i] == x
  ensures forall i :: n <= i < l ==> a[i] > x
  ensures forall i :: l <= i < a.Length ==> a[i] == old(a[i])
{
  m, n := s, s;
  var k := l - 1;

  while (n <= k)
    invariant s <= m <= n <= l
    invariant s - 1 <= k <= l - 1
    invariant forall i :: 0 <= i < s ==> a[i] == old(a[i])
    invariant forall i :: s <= i < m ==> a[i] < x
    invariant forall i :: m <= i < n ==> a[i] == x
    invariant forall i :: k + 1 <= i < l ==> a[i] > x
    invariant forall i :: l <= i < a.Length ==> a[i] == old(a[i])
  {
    if (a[n] < x) {
      a[m], a[n] := a[n], a[m];
      m, n := m + 1, n + 1;
    } else if (a[n] > x) {
      a[n], a[k] := a[k], a[n];
      k := k - 1;
    } else {
      n := n + 1;
    }
  }
}
