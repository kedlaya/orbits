# Updates

We document here some changes to this code relative to [the original version found here](https://www.github.com/kedlaya/same-class-number).

- The function `group_retract` now contains only the graph creation, with the core computation moved to `retract_from_graph`.
-  In `retract_from_graph`, we use `collections.deque` to implement the FIFO queue. We also provide the option `forward_only` which provides a speedup when it is known that every weakly connected component of the input digraph is strongly connected (e.g., for Cayley digraphs).
-  The class `GroupRetract` and subclass `CayleyGroupRetract` have been introduced. The latter includes the function `stabilizer`; consequently, it is now optional to provide a method `stabilizer` in the argument `methods` of `extend_orbit_tree`.