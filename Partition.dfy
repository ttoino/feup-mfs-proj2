method Partition(a: array<int>, left: nat, right: nat, x: int)
  returns (m: nat, n: nat)
  modifies a
  requires 0 <= left < right <= a.Length
  ensures left <= m <= n <= right
  ensures a[..left] == old(a[..left])
  ensures forall i | i in a[left..m] :: i < x
  ensures forall i | i in a[m..n] :: i == x
  ensures forall i | i in a[n..right] :: i > x
  ensures a[right..] == old(a[right..])
  ensures forall i | i in a[left..right] :: i in old(a[left..right])
  ensures x in a[left..right] ==> m < n
{
  m, n := left, left;
  var k := right - 1;

  while (n <= k)
    invariant left <= m <= n <= right
    invariant left - 1 <= k <= right - 1
    invariant a[..left] == old(a[..left])
    invariant forall i | left <= i < m :: a[i] < x
    invariant forall i | m <= i < n :: a[i] == x
    invariant forall i | k + 1 <= i < right :: a[i] > x
    invariant a[right..] == old(a[right..])
    invariant forall i | i in a[left..right] :: i in old(a[left..right])
    invariant x in a[left..n] ==> m < n
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
