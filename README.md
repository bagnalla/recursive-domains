# recursive-domains

![](https://upload.wikimedia.org/wikipedia/commons/thumb/1/1f/Pythagoras_Tree_Colored.png/220px-Pythagoras_Tree_Colored.png "Pythagoras tree")

This is a purely constructive Coq development for computing solutions
to recursive domain equations as colimits (i.e., suprema) of ω-chains
in the category **Cpo**<sup>ep</sup> (objects are CPOs and morphisms
are embedding-projection pairs).

It is similar to defining a recursive type as the fixed point of a
functor F (the initial F-algebra), but the resulting type is a CPO
with a constructive supremum operation.

A common construction (of, e.g., recursive functions) within a CPO (an
ordered set formalizing a datatype) is to take the supremum of an
ascending chain (ω-chain) of elements of the CPO. The intuition is
that each element of the chain is a better approximation than its
predecessor of the value we are trying to approximate. The chain tends
toward a limit which can be obtained by taking its supremum.

We define a chain by giving some finite generating function which
produces each new element of the chain as a function of its
predecessor, starting from a bottom element ⊥. The limit of the
sequence induced by ths generating function may be infinite, so in
effect this is merely a way of describing potentially infinite values
in finite terms (not so much different from the use of loops or
recursion in programming languages).

This idea can be lifted up a level, so that instead of defining a
chain within a particular CPO, we define a chain of CPOs within
**Cpo**, the category of CPOs. We first generalize some notions in
terms of category theory to ease the transition.

Now, an ω-chain in **Cpo** is technically a diagram (indexed by the
preorder category of natural numbers) in **Cpo**, and the supremum of
the chain is the colimiting cocone of the diagram. The generating
function is now a functor (similar to initial algebra constructions),
which induces an ω-chain produced by iterative application of the
functor starting from ⊥ (the unit type, which is the initial object in
**Cpo**). The colimit of such a diagram is itself an object in
**Cpo**, and is exactly the one we are hoping to obtain.

Due to technical issues related to contravariance of the first
argument of the function space functor, we move from **Cpo**, in which
the morphisms are Scott continuous mappings, to the category
**Cpo**<sup>ep</sup>, in which the morphisms are embedding-projection
pairs instead.

An embedding-projection pair between two CPOs A and B is a pair of
continuous mappings:
* embed : A → B
* proj : B → A

such that:

* proj ∘ embed = id<sub>A</sub>
* embed ∘ proj ≤ id<sub>A</sub>

witnessing the fact that B is in some sense a better approximation
than A (A ⊑ B), because A can be faithfully embedded (preserving
order) within B.

Given any ω-chain C in **Cpo**<sup>ep</sup>, we can construct its
colimit as the type of infinite chains such that, for every chain, the
ith element has type C<sub>i</sub>, and is equal to the projection of
its successor x<sub>i</sub> = proj x<sub>i+1</sub>. This is sometimes
called the *projective limit* of the chain.

One necessary condition on the functors used in this construction is
that they are *continuous* functors, in the sense that they preserve
colimits. We use a slightly weird version of this continuity property,
which suffices for our needs but lacks the full generality of the
usual one.

## TL;DR

A user of this library can define a functor F using the provided
functor combinators, and apply the projective limit construction to
obtain a type μF (along with an order relation and constructive
supremum operation) which is the solution (unique up to isomorphism)
to the following isomorphism (we may loosely call it an equation):

X ≃ F X

The user also receives two continuous mappings, fold and unfold,
witnessing this isomorphism:

* fold : X → F X
* unfold : F X → X


## Supported functors:
* constant
* identity
* product (bifunctor)
* continuous function space (bifunctor)

TODO: there are still a few admits in ProjectiveLimit.v, mostly
related to an operation that is theoretically trivial but annoyingly
difficult to define in Coq.
