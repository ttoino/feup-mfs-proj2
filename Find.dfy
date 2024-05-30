include "Partition.dfy"

// Find the minimum value in an array
ghost method min(a: array<int>) returns (m: int)
  requires a.Length > 0 // precondition: the array must have at least one element
  ensures forall i | 0 <= i < a.Length :: m <= a[i] // postcondition: m is less than or equal to all elements in the array
{
  m := a[0];
  var i := 1;
  while i < a.Length
    invariant 1 <= i <= a.Length // invariant: i is within the bounds of the array
    invariant forall j | 0 <= j < i :: m <= a[j] // invariant: m is the minimum of the first i elements
  {
    if a[i] < m { // update m if a smaller element is found
      m := a[i];
    }
    i := i + 1; // move to the next element
  }
}

// Find the maximum value in an array
ghost method max(a: array<int>) returns (m: int)
  requires a.Length > 0 // precondition: the array must have at least one element
  ensures forall i | 0 <= i < a.Length :: a[i] <= m // postcondition: m is greater than or equal to all elements in the array
{
  m := a[0];
  var i := 1;
  while i < a.Length
    invariant 1 <= i <= a.Length // invariant: i is within the bounds of the array
    invariant forall j | 0 <= j < i :: a[j] <= m // invariant: m is the maximum of the first i elements
  {
    if a[i] > m { // update m if a larger element is found
      m := a[i];
    }
    i := i + 1; // move to the next element
  }
}

// Find the k-th smallest element in an array
method Find(a: array<int>, k: nat)
  returns (x: int)
  modifies a // the method modifies the array a
  requires 0 <= k < a.Length // precondition: k must be within the bounds of the array
  ensures forall i | i in a[..k] :: i <= x // postcondition: all elements before k are less than or equal to x
  ensures forall i | i in a[k..] :: i >= x // postcondition: all elements from k onwards are greater than or equal to x
  ensures a[k] == x // postcondition: the k-th element is x
{
  var left: nat, right: nat := 0, a.Length;
  ghost var start := min(a); // the minimum value in the array
  ghost var end := max(a); // the maximum value in the array

  while true
    decreases right - left // the loop decreases the range size
    invariant 0 <= left <= k < right <= a.Length // invariant: k is within the current range [left, right]
    invariant forall i | i in a[..left] :: i <= start // invariant: all elements before left are less than or equal to start
    invariant forall i | i in a[left..right] :: start <= i <= end // invariant: all elements in the current range are between start and end
    invariant forall i | i in a[right..] :: i >= end // invariant: all elements after right are greater than or equal to end
  {
    var pivot: nat :| left <= pivot < right; // choose a pivot within the bounds

    var value := a[pivot];
    assert value in a[left..right];
    assert start <= value <= end;
    assert forall i | i in a[left..right] :: start <= i <= end;
    // partittion the array around the pivot value
    var startIndex: nat, endIndex: nat := Partition(a, left, right, value);
    assert start <= value <= end;
    assert forall i | i in a[left..right] :: start <= i <= end;

    // if k is within the range of elements equal to the pivot, the k-th smallest element is within this range
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
    } else if (k < startIndex) {       // if k is in the left partition
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
    } else { // if k is in the right partition
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
  // after partitioning, the k-th element is in its correct position
  x := a[k]; // assign the k-th smallest element to x
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
