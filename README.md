# Logical Relations for Termination-Insensitive Noninterference

We present an expressive information-flow control type system with recursive
types, existential types, label polymorphism, and impredicative type
polymorphism for a higher-order programming language with higher-order state. We
give a novel semantic model of this type system and show that well-typed
programs satisfy termination-insensitive noninterference. Our semantic approach
supports compositional integration of syntactically well-typed and syntactically
ill-typed - but semantically sound - components, which we demonstrate through
several interesting examples.

We define our model using logical relations on top of the
[Iris](https://iris-project.org) program logic framework. To capture
termination-insensitivity, we develop a novel re-usable theory of Modal Weakest
Preconditions. We formalize all of our theory and examples on top of the Iris
program logic framework in the Coq proof assistant.

## Coq development

The development depends on

- `coq`
- `coq-iris`
- `coq-stdpp`
- `coq-autosubst`
- `coq-iris-string-ident`

See the `opam` file for the specific versions required.

To obtain the dependencies, you have to add the following Coq opam repositories:

    opam repo add coq-released https://coq.inria.fr/opam/released
    opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git

Once you got opam set up, run `opam update` followed by `make build-dep` to
install the right versions of the dependencies.

Run `make -jN` to build the full development, where `N` is the number of your
CPU cores.
