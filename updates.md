# Updates

We document here some changes to this code relative to [the original version found here](https://www.github.com/kedlaya/same-class-number).

-  The class `GroupRetract` and subclass `CayleyGroupRetract` have been introduced. The latter includes the function `stabilizer`; as a result, specifying a function `stabilizer` function when creating an orbit lookup tree is now optional (but still supported).
-  We no longer instantiate any Sage graphs, saving some overhead.
-  The class `OrbitLookupTree` has been introduced. The methods `extend`, `green_nodes`, `orbit_rep` correspond to the old functions  `build_orbit_tree`, `green_nodes`, `orbit_rep_from_tree`; these are available in the file `orbits-legacy.sage` for backward compatibility.