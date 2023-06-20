# :seedling: The Sprout SMT solver 

Sprout is a baby, verified implementation of the [CDSAT](https://hal.science/hal-01615830/document) (seedy-SAT) SMT solving algorithm. 
It is verified using [Creusot](https://github.com/xldenis/creusot).

The key feature of Sprout is its verified implementation of the core CDSAT loop, including conflict resolution. 
Additionally it contains two naive implementations of theories for boolean logic and linear rational arithmetic.
