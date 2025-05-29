# Formalization of Computability Theory

An ongoing effort to formalize computability theory notions involving subsets of ℕ.

- Primitive recursive (PR), computable (Comp), and partial recursive (computably enumerable) (CE) sets are all defined
-  PR -> Comp -> CE
- ℕ, the empty set, singletons, finite, and cofinite sets are primitive recursive
- PR, Comp, and CE are closed under union and intersection
- PR and Comp are closed under complement and set difference
- CE is closed under set difference by Comp sets
- CE is closed under finite symmetric difference

- Use functions ϕ_e and enumerable set W_e are defined from Halting.lean
- Basic lemmata about them are proven

- immunity and cohesiveness are defined, with various lemmata

To do:
- every c.e. set contains a computable set
- major subsets
- the relativized arithmetic hierarchy