# Logical Relations for Termination-Insensitive Noninterference
[![Build Status](https://travis-ci.com/logsem/iris-tini.svg?branch=master)](https://travis-ci.com/logsem/iris-tini)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.4068072.svg)](https://doi.org/10.5281/zenodo.4068072)

A mechanized logical relations model for an expressive information-flow control
type system with recursive types, existential types, label polymorphism, and
impredicative type polymorphism for a higher-order programming language with
higher-order state. The semantic model of the type system can be used to show
that well-typed programs satisfy termination-insensitive noninterference but
also to show that composing syntactically well-typed and syntactically
ill-typed---but semantically sound---components is secure.

The model is defined using the [Iris](https://iris-project.org) program logic
framework. To capture termination-insensitivity, we make us of our [theory of
Modal Weakest Precondition](https://github.com/logsem/modal-weakestpre/). We
formalize all of our theory and examples on top of the Iris program logic
framework in the Coq proof assistant.

This development accompanies the paper [Mechanized Logical Relations for
Termination-Insensitive
Noninterference](https://cs.au.dk/~gregersen/papers/2021-tiniris.pdf) published
at POPL 2021.

## Building the theory

The project can be built locally or by using the provided
[Dockerfile](Dockerfile), see the [Using Docker](/#using-docker)
section for details on the latter. The development uses
[modal-weakestpre](https://github.com/logsem/modal-weakestpre/) as a git
submodule; remember to run

    git submodule update --init --recursive
    
after cloning the repository to initialize it. Alternatively, you can clone the
repository using the `--recurse-submodules` flag.

### Prerequisites 

The project is known to compile with:

- Coq 8.12.0
- Development versions of [Iris](https://gitlab.mpi-sws.org/iris/iris/) and
  [std++](https://gitlab.mpi-sws.org/iris/stdpp) as specified in the
  [iris-tini.opam](iris-tini.opam) file
- [Autosubst 1](https://github.com/uds-psl/autosubst)

The dependencies can be obtained using opam

1. Install [opam](https://opam.ocaml.org/doc/Install.html) 
2. To obtain the dependencies, you have to add the following repositories to the
   registry by invoking

        opam repo add coq-released https://coq.inria.fr/opam/released
        opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git
        opam update

3. Run `make build-dep` to install the right versions of the dependencies.

### Building

Run `make -jN` to build the full development, where `N` is the number of CPU
cores on your machine.

### Using Docker

The development can be built using Docker.

1. Install [Docker](https://docs.docker.com/get-docker/)
2. Run `make docker-build` to build the Docker image [Dockerfile](Dockerfile) that
   compiles the development using pre-compiled dependencies.
3. Optionally, you can execute `docker run -i -t iris-tini-compile` to get an
   interactive shell. 

To speed up compilation time, the dependencies have been prepared and compiled
separately in [Dockerfile.deps](Dockerfile.deps) and published in a Dockerhub
[repository](https://hub.docker.com/repository/docker/simongregersen/iris-tini). This
image can be built locally by running `make docker-build-deps` if needed.

## Documentation

Documentation can be generated using
[coqdoc](https://coq.inria.fr/refman/using/tools/coqdoc.html) by running `make
html`. [doc.html](doc.html) provides an entry and overview of the generated
documentation.

## Source organization

### Language and semantic model

- [theories/lambda_sec/lattice.v](theories/lambda_sec/lattice.v): theory of join
  semilattices, including the induced lattice ordering
- [theories/lambda_sec/lang.v](theories/lambda_sec/lang.v): the language and
  operational semantics
- [theories/lambda_sec/types.v](theories/lambda_sec/types.v): syntactic types,
  substitution principles, and syntactic flows-to relation
- [theories/lambda_sec/notation.v](theories/lambda_sec/notation.v): notation for
  writing programs and types
- [theories/lambda_sec/typing.v](theories/lambda_sec/typing.v): subtyping and
  typing relation
- [theories/lambda_sec/rules_unary.v](theories/lambda_sec/rules_unary.v): unary
  language lemmas
- [theories/lambda_sec/logrel_unary.v](theories/lambda_sec/logrel_unary.v):
  unary logical relation
- [theories/lambda_sec/fundamental_unary.v](theories/lambda_sec/logrel_unary.v):
  unary fundamental theorem of logical relations
- [theories/lambda_sec/rules_binary.v](theories/lambda_sec/rules_binary.v):
  binary language lemmas
- [theories/lambda_sec/logrel_binary.v](theories/lambda_sec/logrel_binary.v):
  binary logical relation
- [theories/lambda_sec/fundamental_binary.v](theories/lambda_sec/logrel_binary.v):
  binary fundamental theorem of logical relations
- [theories/lambda_sec/noninterference.v](theories/lambda_sec/noninterference.v):
  noninterference statement and proof, both for a generic lattice and a
  two-point lattice
  
### Modal Weakest Precondition Theory

Below we highlight the parts of the modal weakest precondition theory that is
relevant for this development.

- [modal-weakestpre/theories/mwp.v](https://github.com/logsem/modal-weakestpre/tree/main/theories/mwp.v):
  definition of the generic modal weakest precondition
- [modal-weakestpre/theories/mwp_adequacy.v](https://github.com/logsem/modal-weakestpre/tree/main/theories/mwp_adequacy.v):
  adequacy theorem of the generic modal weakest precondition
- [modal-weakestpre/theories/mwp_triple.v](https://github.com/logsem/modal-weakestpre/tree/main/theories/mwp_triple.v):
  a Hoare-triple definition for modal weakest precondition
- [modal-weakestpre/theories/mwp_modalities/mwp_step_fupd.v](https://github.com/logsem/modal-weakestpre/tree/main/theories/mwp_modalities/mwp_step_fupd.v):
  step-taking update modality MWP instance used for the unary relation
- [modal-weakestpre/theories/mwp_modalities/mwp_fupd.v](https://github.com/logsem/modal-weakestpre/tree/main/theories/mwp_modalities/mwp_fupd.v):
  update modality MWP instance
- [modal-weakestpre/theories/mwp_modalities/ni_logrel/mwp_right.v](https://github.com/logsem/modal-weakestpre/tree/main/theories/mwp_modalities/ni_logrel/mwp_right.v):
  inner MWP instance for the binary relation
- [modal-weakestpre/theories/mwp_modalities/ni_logrel/mwp_left.v](https://github.com/logsem/modal-weakestpre/tree/main/theories/mwp_modalities/ni_logrel/mwp_left.v):
  binary MWP instance for the binary relation
- [modal-weakestpre/theories/mwp_modalities/ni_logrel/ni_logrel_lemmas.v](https://github.com/logsem/modal-weakestpre/tree/main/theories/mwp_modalities/ni_logrel/ni_logrel_lemmas.v):
  lemmas for the interaction between the step-taking update modality instance
  (unary) and the binary MWP instance
- [modal-weakestpre/theories/mwp_modalities/ni_logrel/mwp_logrel_fupd.v](https://github.com/logsem/modal-weakestpre/tree/main/theories/mwp_modalities/ni_logrel/mwp_logrel_fupd.v):
  binary MWP instance used for the
  [theories/examples/refs.v](theories/examples/refs.v) and
  [theories/examples/refs_implicit.v](theories/examples/refs_implicit.v) example
  that allows invariants to be kept open for the full execution
  
### Examples 
The [theories/examples](theories/examples) folder includes multiple case
studies, among others, about [value
dependency](theories/examples/value_dependent.v), [the awkward
example](theories/examples/awkward.v), and
[parametricity](theories/examples/parametricity.v).
