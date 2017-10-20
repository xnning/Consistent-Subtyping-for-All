This repository must be built with Coq 8.5pl3.

It requires the Coq library [TLC](http://www.chargueraud.org/softs/tlc/), which
provides in particular enhanced tactics, and representation for variables and
finite sets of variables. For ease of use, we include the source files
under [tlc/](./tlc/) directory.

This work checks with Coq's native theory -- it includes no Axioms or other
extensions (apart from the TLC library).

# Roadmap #

[decl-higher-rank/](./decl-higher-rank) contains all of the Coq development. Run
`make` will check the proofs.

+ `DeclDef.v` - Definitions of the declarative system.
+ `DeclProp.v` - Lemmas of subtyping, consistency, consistent subtyping.
+ `PBCDef.v` - Definitions of the Polymorphic Blame Calculus.
+ `Criteria.v` - Proofs of the correctness criteria
+ `Translation.v` - Proofs of the safety of type-directed translation.

# Lemmas and Theorems in the Paper #

+ `Proposition 3` - `DeclProp.v/dconsist_directed`, `dconsist_directd_reverse`
+ `Theorem 1`  - `DeclProp.v/dconsub_prop1`, `DeclProp/dconsub_prop2`
+ `Lemma A.1` - `DeclProp.v/dconsub_mono_eq`
+ `Lemma 1` - `Translation.v/dmatch_pcompatible`
+ `Lemma 2` - `Translation.v/dconsub_pcompatible`
+ `Theorem 2` - `Translation.v/d2ptyping_type`,
+ `Lemma 3` - `Criteria.v/conservative_extension`, `Criteria.v/monotonicity_precision`, `Criteria.v/monotonicity_cast_insertion`, `Translation.v/d2ptyping_typ`, `Translation.v/dtyping_d2ptyping`


