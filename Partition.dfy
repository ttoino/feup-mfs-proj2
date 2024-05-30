method Partition(a: array<int>, left: nat, right: nat, x: int)
  returns (m: nat, n: nat)
  modifies a //the method modifies the array a
  requires 0 <= left < right <= a.Length // precondition: left and right indices are within array bounds
  ensures left <= m <= n <= right // postcondition: m and n are within the specified segment
  ensures a[..left] == old(a[..left]) // postcondition: elements before the segment remain unchanged
  ensures forall i | i in a[left..m] :: i < x // postcondition: all elements in the first partition are less than x
  ensures forall i | i in a[m..n] :: i == x // postcondition: all elements in the second partition are equal to x
  ensures forall i | i in a[n..right] :: i > x // postcondition: all elements in the third partition are greater than x
  ensures a[right..] == old(a[right..]) // postcondition: elements after the segment remain unchanged
  ensures forall i | i in a[left..right] :: i in old(a[left..right]) // postcondition: all elements in the segment are from the original segment
  ensures x in a[left..right] ==> m < n // postcondition: if x is in the segment, there is at least one element equal to x (because m will be lower than n)
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
    // if the current element is less than x -> swap elements at m and n and move both m and n to the right
    if (a[n] < x) {
      a[m], a[n] := a[n], a[m];
      m, n := m + 1, n + 1;
    } else if (a[n] > x) { // if the current element is greater than x -> swap elements at n and k and move k to the left
      a[n], a[k] := a[k], a[n];
      k := k - 1;
    } else { // If the current element is equal to x -> move n to the right
      n := n + 1;
    }
  }
}
