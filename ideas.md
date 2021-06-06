# Ideas

- Reorder partial definitions so that base case can be either before or after
  the recursive case in the file. i.e.
  `rec n = rec (n-1); rec 1 = 1;`
  the order of these should be swapped, so that we check the base case first.
    - Does this make sense?????
