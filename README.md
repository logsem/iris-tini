# Logical Relations for Termination-Insensitive Noninterference
[![Build Status](https://travis-ci.com/logsem/iris-tini.svg?branch=master)](https://travis-ci.com/logsem/iris-tini)

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

## Building the theory

The project can be built locally or by using the provided
[Dockerfile](Dockerfile), see the [Using Docker](/#using-docker) section for
details on the latter. The development uses
[modal-weakestpre](https://github.com/logsem/modal-weakestpre/) as a git
sub-module; remember to run

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

The dependencies can be obtained using opam; see [this
guide](https://opam.ocaml.org/doc/Install.html) for how to install opam. To
obtain the dependencies, you have to add the following repositories to the opam
registry by invoking

    opam repo add coq-released https://coq.inria.fr/opam/released
    opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git
    opam update

Once you got opam set up, run `make build-dep` to install the right versions of
the dependencies.

### Building

Run `make -jN` to build the full development, where `N` is the number of CPU
cores on your machine.

### Using Docker

The development can be built using
[Docker](https://docs.docker.com/get-docker/). To speed up compilation time, the
dependencies have been prepared and compiled separately in
[Dockerfile.deps](Dockerfile.deps) and published in a Dockerhub
[repository](https://hub.docker.com/repository/docker/simongregersen/modal-weakestpre). This
image can be built locally by running `make docker-build-deps`.

Run `make docker-build` to build [Dockerfile](Dockerfile) and the development
with the pre-compiled dependencies.

## Documentation

Documentation can be generated using
[coqdoc](https://coq.inria.fr/refman/using/tools/coqdoc.html) by running `make
html`. Afterwards, a [table of contents](html/toc.html) is generated from which
the documentation can be accessed.
