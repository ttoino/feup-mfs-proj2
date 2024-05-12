include "Partition.dfy"

method Find(a: array<int>, k: nat)
  returns (x: int)
  modifies a
  requires 0 <= k < a.Length
  ensures forall i | 0 <= i <= k :: a[i] <= x
  ensures forall i | k < i < a.Length :: a[i] >= x
  ensures a[k] == x
{
  var left: nat, right: nat := 0, a.Length;

  while true
    decreases right - left
    invariant 0 <= left <= k < right <= a.Length
    invariant forall i | 0 <= i < left :: a[i] <= a[k]
    invariant forall i | right <= i < a.Length :: a[i] >= a[k]
  {
    var pivot: nat :| left <= pivot < right;

    var startIndex: nat, endIndex: nat := Partition(a, left, right, a[pivot]);
    assume {:axiom} startIndex < endIndex;

    assume {:axiom} forall i | 0 <= i < left :: a[i] <= a[k];
    assume {:axiom} forall i | right <= i < a.Length :: a[i] >= a[k];

    if (startIndex <= k < endIndex) {
      break;
    } else if (k < startIndex) {
      right := startIndex;
    } else {
      left := endIndex;
    }
  }

  x := a[k];
}
