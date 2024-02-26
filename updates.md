# Updates

We document here some changes to this code relative to [the original version found here](https://www.github.com/kedlaya/same-class-number). See also [this writeup](https://github.com/kedlaya/orbits/blob/main/orbits.pdf).

-  The class `CayleyGroupRetract` have been introduced to solve the orbit-stabilizer problem for a group action.
-  We no longer instantiate any Sage graphs, saving some overhead.
-  The class `OrbitLookupTree` has been introduced. The methods `extend`, `green_nodes`, `orbit_rep` correspond to the old functions  `build_orbit_tree`, `green_nodes`, `orbit_rep_from_tree`; these are available in the file `orbits-legacy.sage` for backward compatibility.
- The `stabilizer` method is no longer supported.
- The option `linear` is provided to specify that we want the induced action on subspaces rather than subsets. Currently this requires the base field to be F_2.
- The computation of orbit representatives now supports batch execution.
- In the computation of the extension of an orbit lookup tree from level n to level n+1, the second step has been simplified; instead of forming a group retract, we directly identify the orbits and stabilizers. We also use batch computation of orbit representatives to save some work.