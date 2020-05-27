# Consistent Subtyping for All

This is the artifact for paper *Consistent Subtyping for All*,
published in [ESOP 2018](https://etaps.org/2018/esop),
and its significant extended version, published in
[TOPLAS](https://dl.acm.org/journal/toplas).

> Consistent subtyping is employed in some gradual type systems to validate type
> conversions. The original definition by Siek and Taha serves as a guideline for
> designing gradual type systems with subtyping. Polymorphic types à la System F
> also induce a subtyping relation that relates polymorphic types to their
> instantiations. However, Siek and Taha’s definition is not adequate for
> polymorphic subtyping. The first goal of this article is to propose a
> generalization of consistent subtyping that is adequate for polymorphic
> subtyping and subsumes the original definition by Siek and Taha. The new
> definition of consistent subtyping provides novel insights with respect to
> previous polymorphic gradual type systems, which did not employ consistent
> subtyping. The second goal of this article is to present a gradually typed
> calculus for implicit (higher-rank) polymorphism that uses our new notion of
> consistent subtyping. We develop both declarative and (bidirectional)
> algorithmic versions for the type system. The algorithmic version employs
> techniques developed by Dunfield and Krishnaswami for higher-rank polymorphism
> to deal with instantiation. We prove that the new calculus satisfies all static
> aspects of the refined criteria for gradual typing. We also study an extension
> of the type system with static and gradual type parameters, in an attempt to
> support a variant of the dynamic criterion for gradual typing. Assuming a
> coherence conjecture for the extended calculus, we show that the dynamic gradual
> guarantee of our source language can be reduced to that of λB, which, at the
> time of writing, is still an open question. Most of the metatheory of this
> article, except some manual proofs for the algorithmic type system and
> extensions, has been mechanically formalized using the Coq proof assistant.


## Road Map

+ [paper_long.pdf](./paper_long.pdf): Full paper with the appendix for the journal publication.
+ [coq/](./coq) contains all of the Coq development.
+ [impl/](./impl) contains the implementation for the type checker.
