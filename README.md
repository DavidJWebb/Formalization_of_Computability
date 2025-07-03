# Formalization of Computability Theory

An ongoing effort to formalize computability theory notions involving subsets of ℕ.

**Primitive Recursiveness**
- Filtering for elements meeting a decidable criterion is primitive recursive
- Bounded quantifiers are primitive recursive

**Sets**
- Primitive recursive (PR), computable (Comp), and partial recursive (computably enumerable) (CE) sets are all defined
-  PR -> Comp -> CE
- ℕ, the empty set, singletons, finite, and cofinite sets are primitive recursive
- PR, Comp, and CE are closed under union and intersection
- PR and Comp are closed under complement and set difference
- CE is closed under set difference by Comp sets
- CE is closed under finite symmetric difference

**ϕ and W**
- Use functions ϕ_e and enumerable sets W_e are defined from Halting.lean
- Partial versions ϕ_{e, s} and W_{e, s} are defined
- Primitive recursiveness, partial recursiveness, and computability of the above are defined
- The runtime of a computatation ϕ_e is defined
- Basic lemmata about the above are proven

**W as a Sequence**
- WPrefix e s is the list of elements for which ϕ_{e,s} halts, *in the order that they halted*
- Restricting enumerations to one element per stage, enter_queue e s is the list of elements that have halted, but are waiting to be enumerated 
- new_element e s is the element enumerated at stage s (if any)
- Wenum e is the function s => new_element e s
- ϕ_e(n) halts iff n is in the range of Wenum e
- W_e is finite iff for all large enough s, Wenum e s = Option.none

**Classical Computability Theory**
- Immunity and cohesiveness are defined, with various lemmata (some of whose proofs rely on the next unproven fact)

**To do:**
- increasing c.e. sets are computable
- every c.e. set contains a computable set
- relativizations
- major subsets