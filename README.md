# Formalization of Computability Theory

An ongoing effort to formalize computability theory notions involving subsets of ℕ.

**Sets**
- Primitive recursive (PR), computable (Comp), and partial recursive (computably enumerable) (CE) sets are all defined
-  PR -> Comp -> CE
- ℕ, the empty set, singletons, finite, and cofinite sets are primitive recursive
- PR, Comp, and CE are closed under union and intersection
- PR and Comp are closed under complement and set difference
- CE is closed under set difference by Comp sets
- CE is closed under finite symmetric difference

**ϕ and W**
- Use functions ϕ_e and enumerable set W_e are defined from Halting.lean
- The runtime of a computatation ϕ_e is defined
- Basic lemmata about the above are proven
- W_enum_prefix e s is the list of elements for which ϕ_{e,s} halts, *in the order that they halted*

- Immunity and cohesiveness are defined, with various lemmata (some of whose proofs rely on the next unproven fact)

To do:
- every c.e. set contains a computable set
- major subsets
- the relativized arithmetic hierarchy