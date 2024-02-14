# orbits

This repository contains code for the following problem in computational group theory: given a finite group G acting on a finite set S, compute orbit representatives for the induced action of G on k-element subsets of S. We use the method of *orbit lookup trees* described in the appendix of:
K.S. Kedlaya, The relative class number one problem for function fields, III; and originally implemented in [the repository associated to that paper](https://www.github.com/kedlaya/same-class-number). Some modifications to the original method are described [here](./updates.md).

We currently provide an implementation in SageMath, which in turn calls on GAP for the underlying group theory computations (primarily computing subgroups from generators).

All files in this repository are provided under a [Creative Commons CC BY 4.0 license](https://creativecommons.org/licenses/by/4.0).