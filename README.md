# Mechanized Logical Relations for Termination-Insensitive Noninterference.

  We present an expressive information-flow control type system with recursive
  types, existential types, label polymorphism, and impredicative type
  polymorphism for a higher-order programming language with higher-order state.
  We give a novel semantic model of this type system and show that well-typed
  programs satisfy termination-insensitive noninterference. Our semantic
  approach supports compositional integration of syntactically well-typed and
  syntactically ill-typed---but semantically sound---components, which we
  demonstrate through several interesting examples. We define our model using
  logical relations on top of the Iris program logic framework. To capture
  termination-insensitivity, we develop a novel re-usable theory of Modal
  Weakest Preconditions. We formalize all of our theory and examples on top of
  the Iris program logic framework in the Coq proof assistant.

# Coq formalization

The development is known to compile with:

- `coq`: version `8.11.1`
- `coq-iris` : version `dev.2020-04-09.2.962637df`
- `coq-stdpp` : version `dev.2020-04-03.1.eeef6250`
- `coq-autosubst`
- `coq-iris-string-ident`

To install the dependencies, you have to add the following opam repositories:

    opam repo add coq-released https://coq.inria.fr/opam/released
    opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git

Once you got opam set up, run `opam update` followed by `make build-dep` to
install the right versions of the dependencies.

Run `make -jN` to build the full development, where `N` is the number of your
CPU cores.

## Modal Weakest Precondition Theory
The *Modal Weakest Precondition* theory is in our Coq formalization called
*If-Convergent* (IC).

- [Overview of the full development](html-if-convergent/toc.html).
- The general definition of the IC predicate (Definition 3.4) is defined in
  [IC.v](html-if-convergent/IC.if_convergent.IC.html).
- All general derived proof rules for program reasoning are defined in
  [IC_lifting.v](html-if-convergent/IC.if_convergent.IC_lifting.html).
- The adequacy statement is stated and proved in
  [IC_adequacy.v](html-if-convergent/IC.if_convergent.IC_adequacy.html).
- The example predicate (Example 3.1) is defined in [IC_fupd.v](html-if-convergent/IC.if_convergent.derived.IC_fupd.html).
- The unary predicate (Example 3.2) used in our logical-relations model is
  defined in
  [IC_step_fupd.v](html-if-convergent/IC.if_convergent.derived.IC_step_fupd.html).
- The binary predicate (Example 3.5) used in our logical-relations mode is
  defined in
  [IC_left.v](html-if-convergent/IC.if_convergent.derived.ni_logrel.IC_left.html);
  the inner predicate in
  [IC_right.v](html-if-convergent/IC.if_convergent.derived.ni_logrel.IC_right.html)
- The binary predicate used in Section 5 is defined in
  [IC_logrel_fupd.v](html-if-convergent/IC.if_convergent.derived.ni_logrel.IC_logrel_fupd.html)
- Lemmas about the interactions between the unary and binary predicates
  (e.g. Lemma 3.7 and Lemma 5.1) are found in
  [ni_logrel_lemmas.v](html-if-convergent/IC.if_convergent.derived.ni_logrel.ni_logrel_lemmas.html)
  and
  [ni_logrel_fupd_lemmas.v](html-if-convergent/IC.if_convergent.derived.ni_logrel.ni_logrel_fupd_lemmas.html)

## Noninterference Development

- [Overview of the full development](html-logrel-ifc/toc.html).
- Our language of study is defined in
  [lang.v](html-logrel-ifc/logrel_ifc.lambda_sec.lang.html).
- The types and type system are defined in
  [types.v](html-logrel-ifc/logrel_ifc.lambda_sec.types.html) and
  [typing.v](html-logrel-ifc/logrel_ifc.lambda_sec.typing.html), respectively.
- The unary logical relation is defined in
  [logrel_unary.v](html-logrel-ifc/logrel_ifc.lambda_sec.logrel_unary.html) and
  its fundamental theorem is stated and proved in
  [fundamental_unary.v](html-logrel-ifc/logrel_ifc.lambda_sec.fundamental_unary.html).
- The binary logical relation is defined in
  [logrel_binary.v](html-logrel-ifc/logrel_ifc.lambda_sec.logrel_binary.html) and
  its fundamental theorem is stated and proved in
  [fundamental_binary.v](html-logrel-ifc/logrel_ifc.lambda_sec.fundamental_binary.html).
- Termination-insensitive noninterference is proved in
  [noninterference.v](html-logrel-ifc/logrel_ifc.lambda_sec.noninterference.html).
- The introductory examples are found in
  [arith.v](html-logrel-ifc/logrel_ifc.examples.arith.html),
  [refs.v](html-logrel-ifc/logrel_ifc.examples.refs.html), and
  [refs_implicit.v](html-logrel-ifc/logrel_ifc.examples.refs_implicit.html).
- The example from Section 5.1 is found in
  [report.v](html-logrel-ifc/logrel_ifc.examples.report.html).
- The examples from Section 5.2 are found in
  [value_dependent.v](html-logrel-ifc/logrel_ifc.examples.value_dependent.html)
  and
  [value_dependent_pack.v](html-logrel-ifc/logrel_ifc.examples.value_dependent_pack.html).
- The example from Section 5.3 is found in
  [compute_with_cache.v](html-logrel-ifc/logrel_ifc.examples.compute_with_cache.html).
- The parametricity theorems from Section 5.4 are shown in
  [parametricity.v](html-logrel-ifc/logrel_ifc.examples.parametricity.html).
