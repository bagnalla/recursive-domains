# recursive-domains

Solutions to recursive domain equations as colimits in the category
**Cpo**<sup>ep</sup> (the objects are CPOs and the morphisms are
embedding-projection pairs).

This is for defining recursive types from a given functor, similar to
initial algebras but they also come with CPO structure.

Supported functors:
* constant
* identity
* product (bifunctor)
* continuous function space (bifunctor)

The embedding-projection pairs are used to deal with contravariance in
the first argument to the function space functor.

There are still a few admits in ProjectiveLimit.v.