# Ideas

- Reorder partial definitions so that base case can be either before or after
  the recursive case in the file. i.e.
  `map f (x::xs) = f x :: map f xs; map f [] = [];`
  the order of these should be swapped, so that we check the base case first.
