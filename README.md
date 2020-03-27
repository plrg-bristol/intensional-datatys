# Intensional Constraints

Scalable refinement types as a GHC plugin.

The refinement types in this system are a set of constructors, and thus a subset of the algebraic datatype/DSL.

The arguments to the constructors can't change type in a refinement.
For example, with a arithmetic DSL, you could specifiy that the term doesn't contain addition, but you can not distinguish at the type level between the term and subterms.

The algorithm converts subtyping constraints into a graph and reachability problem.
This graph can be then be redueced using the Floyd-Warshall algorithm to provide each function with a mangeable interface.
