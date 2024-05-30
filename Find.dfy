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
    assert value in a[left..right]; // assert that the pivot value is within the current range
    assert start <= value <= end; // assert that the pivot value is between start and end
    assert forall i | i in a[left..right] :: start <= i <= end; // assert that all elements in the current range are between start and end
    var startIndex: nat, endIndex: nat := Partition(a, left, right, value); // partition the array around the pivot value
    assert start <= value <= end; // assert that the pivot value is between start and end (post-partition check)
    assert forall i | i in a[left..right] :: start <= i <= end; // assert that all elements in the current range are between start and end (post-partition check)

    // if k is within the range of elements equal to the pivot, the k-th smallest element is within this range
    if (startIndex <= k < endIndex) {
      assert forall i | i in a[..startIndex] :: i in a[..left] || i in a[left..startIndex]; // assert that all elements before startIndex are either before left or within the left partition
      assert forall i | i in a[..startIndex] :: i <= value; // assert that all elements before startIndex are less than or equal to the pivot value
      assert forall i | i in a[endIndex..] :: i in a[right..] || i in a[endIndex..right]; // assert that all elements after endIndex are either after right or within the right partition
      assert forall i | i in a[endIndex..] :: i >= value; // assert that all elements after endIndex are greater than or equal to the pivot value
      left, right := startIndex, endIndex; // narrow the range to the pivot values
      start, end := value, value; // set start and end to the pivot value
      assert forall i | i in a[..left] :: i <= start; // assert that all elements before left are less than or equal to start (which is now the pivot value)
      assert forall i | i in a[left..right] :: start <= i <= end; // assert that all elements in the range [left, right] are equal to the pivot value
      assert forall i | i in a[right..] :: i >= end; // assert that all elements after right are greater than or equal to end (which is now the pivot value)
      break;
    } else if (k < startIndex) {       // if k is in the left partition
      assert forall i | i in a[left..startIndex] :: i in a[left..right]; // assert that all elements in the left partition are within the current range
      assert forall i | i in a[left..startIndex] :: start <= i <= end; // assert that all elements in the left partition are between start and end
      assert forall i | i in a[left..startIndex] :: start <= i <= value; // assert that all elements in the left partition are less than or equal to the pivot value
      assert forall i | i in a[startIndex..right] :: i in a[startIndex..endIndex] || i in a[endIndex..right]; // assert that all elements in the range [startIndex, right] are either within the equal-to-pivot range or in the right partition
      assert forall i | i in a[startIndex..right] :: i >= value; // assert that all elements in the range [startIndex, right] are greater than or equal to the pivot value
      assert forall i | i in a[right..] :: i >= value; // assert that all elements after right are greater than or equal to the pivot value
      assert forall i | i in a[startIndex..] :: i in a[startIndex..right] || i in a[right..]; // assert that all elements after startIndex are either within the range [startIndex, right] or after right
      assert forall i | i in a[startIndex..] :: i >= value; // assert that all elements after startIndex are greater than or equal to the pivot value
      right := startIndex;
      end := value;
    } else { // if k is in the right partition
      assert forall i | i in a[endIndex..right] :: i in a[left..right]; // assert that all elements in the right partition are within the current range 
      assert forall i | i in a[endIndex..right] :: start <= i <= end; // assert that all elements in the right partition are between start and end
      assert forall i | i in a[endIndex..right] :: value <= i <= end; // assert that all elements in the right partition are greater than or equal to the pivot value
      assert forall i | i in a[left..endIndex] :: i in a[startIndex..endIndex] || i in a[left..startIndex];  // assert that all elements in the range [left, endIndex] are either within the equal-to-pivot range or in the left partition
      assert forall i | i in a[left..endIndex] :: i <= value; // assert that all elements in the range [left, endIndex] are less than or equal to the pivot value
      assert forall i | i in a[..left] :: i <= value; // assert that all elements before left are less than or equal to the pivot value
      assert forall i | i in a[..endIndex] :: i in a[left..endIndex] || i in a[..left]; // assert that all elements before endIndex are either within the range [left, endIndex] or before left
      assert forall i | i in a[..endIndex] :: i <= value;
      left := endIndex;
      start := value;
    }
  }

  assert forall i | i in a[..left] :: i <= start; // assert that all elements before left are less than or equal to start
  assert forall i | i in a[left..right] :: start <= i <= end; // assert that all elements in the current range [left, right] are between start and end
  assert forall i | i in a[right..] :: i >= end; // assert that all elements after right are greater than or equal to end
  assert left <= k < right; // assert that k is within the range [left, right]
  assert start == end;  // assert that start and end are equal (meaning all elements in the current range are the same)
  // after partitioning, the k-th element is in its correct position
  x := a[k]; // assign the k-th smallest element to x
  assert x in a[left..right]; // assert that the k-th element is within the current range [left, right]
  assert start <= x <= end; // assert that x is between start and end
  assert x == start; // assert that x is equal to start
  assert x == end;   // assert that x is equal to end
    // assert that all elements before k are less than or equal to x
  assert forall i | i in a[left..k] :: i in a[left..right];
  assert forall i | i in a[..k] :: i in a[..left] || i in a[left..k];
  assert forall i | i in a[..k] :: i <= x;

  assert forall i | i in a[k..right] :: i in a[left..right]; // assert that all elements from k to right are within the current range [left, right]
  assert forall i | i in a[k..] :: i in a[right..] || i in a[k..right]; // assert that all elements from k onwards are either after right or within the range [k, right]
  assert forall i | i in a[k..] :: i >= x;  // assert that all elements from k onwards are greater than or equal to x
}
