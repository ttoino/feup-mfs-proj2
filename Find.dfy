include "Partition.dfy"

ghost method min(a: array<int>) returns (m: int)
  requires a.Length > 0
  ensures forall i | 0 <= i < a.Length :: m <= a[i]
{
  m := a[0];
  var i := 1;
  while i < a.Length
    invariant 1 <= i <= a.Length
    invariant forall j | 0 <= j < i :: m <= a[j]
  {
    if a[i] < m {
      m := a[i];
    }
    i := i + 1;
  }
}

ghost method max(a: array<int>) returns (m: int)
  requires a.Length > 0
  ensures forall i | 0 <= i < a.Length :: a[i] <= m
{
  m := a[0];
  var i := 1;
  while i < a.Length
    invariant 1 <= i <= a.Length
    invariant forall j | 0 <= j < i :: a[j] <= m
  {
    if a[i] > m {
      m := a[i];
    }
    i := i + 1;
  }
}

method Find(a: array<int>, k: nat)
  returns (x: int)
  modifies a
  requires 0 <= k < a.Length
  ensures forall i | i in a[..k] :: i <= x
  ensures forall i | i in a[k..] :: i >= x
  ensures a[k] == x
{
  var left: nat, right: nat := 0, a.Length;
  ghost var start := min(a);
  ghost var end := max(a);

  while true
    decreases right - left
    invariant 0 <= left <= k < right <= a.Length
    invariant forall i | i in a[..left] :: i <= start
    invariant forall i | i in a[left..right] :: start <= i <= end
    invariant forall i | i in a[right..] :: i >= end
  {
    var pivot: nat :| left <= pivot < right;

    var value := a[pivot];
    assert value in a[left..right];
    assert start <= value <= end;
    assert forall i | i in a[left..right] :: start <= i <= end;
    var startIndex: nat, endIndex: nat := Partition(a, left, right, value);
    assert start <= value <= end;
    assert forall i | i in a[left..right] :: start <= i <= end;

    if (startIndex <= k < endIndex) {
      assert forall i | i in a[..startIndex] :: i in a[..left] || i in a[left..startIndex];
      assert forall i | i in a[..startIndex] :: i <= value;
      assert forall i | i in a[endIndex..] :: i in a[right..] || i in a[endIndex..right];
      assert forall i | i in a[endIndex..] :: i >= value;
      left, right := startIndex, endIndex;
      start, end := value, value;
      assert forall i | i in a[..left] :: i <= start;
      assert forall i | i in a[left..right] :: start <= i <= end;
      assert forall i | i in a[right..] :: i >= end;
      break;
    } else if (k < startIndex) {
      assert forall i | i in a[left..startIndex] :: i in a[left..right];
      assert forall i | i in a[left..startIndex] :: start <= i <= end;
      assert forall i | i in a[left..startIndex] :: start <= i <= value;
      assert forall i | i in a[startIndex..right] :: i in a[startIndex..endIndex] || i in a[endIndex..right];
      assert forall i | i in a[startIndex..right] :: i >= value;
      assert forall i | i in a[right..] :: i >= value;
      assert forall i | i in a[startIndex..] :: i in a[startIndex..right] || i in a[right..];
      assert forall i | i in a[startIndex..] :: i >= value;
      right := startIndex;
      end := value;
    } else {
      assert forall i | i in a[endIndex..right] :: i in a[left..right];
      assert forall i | i in a[endIndex..right] :: start <= i <= end;
      assert forall i | i in a[endIndex..right] :: value <= i <= end;
      assert forall i | i in a[left..endIndex] :: i in a[startIndex..endIndex] || i in a[left..startIndex];
      assert forall i | i in a[left..endIndex] :: i <= value;
      assert forall i | i in a[..left] :: i <= value;
      assert forall i | i in a[..endIndex] :: i in a[left..endIndex] || i in a[..left];
      assert forall i | i in a[..endIndex] :: i <= value;
      left := endIndex;
      start := value;
    }
  }

  assert forall i | i in a[..left] :: i <= start;
  assert forall i | i in a[left..right] :: start <= i <= end;
  assert forall i | i in a[right..] :: i >= end;
  assert left <= k < right;
  assert start == end;
  x := a[k];
  assert x in a[left..right];
  assert start <= x <= end;
  assert x == start;
  assert x == end;
  assert forall i | i in a[left..k] :: i in a[left..right];
  assert forall i | i in a[..k] :: i in a[..left] || i in a[left..k];
  assert forall i | i in a[..k] :: i <= x;
  assert forall i | i in a[k..right] :: i in a[left..right];
  assert forall i | i in a[k..] :: i in a[right..] || i in a[k..right];
  assert forall i | i in a[k..] :: i >= x;
}
