# POPL21 Artifact Evaluation

This document contains instructions for the artifact evaluation reviewers when
evaluating this Coq development.

## Inspecting the development

The modal weakest precondition theory is standalone and available in the
[vendor/modal_weakestpre/theories](vendor/modal_weakestpre/theories) folder.
The logical relations model for proving noninterference is available in the
[theories](theories) folder.

The artifact comes with pre-compiled coqdoc documentation accessible through
[doc.html](doc.html). This document also contains a mapping of the definitions,
examples, and results from the paper to the Coq development.

## Building the development

We recommend compiling the development using Docker. To do this,

1. Make sure you have [Docker](https://docs.docker.com/get-docker/) installed.
2. Run `make docker-build` to build the Docker image.

Optionally, you can follow this by executing `docker run -i -t
iris-tini-compile` to start a container with the freshly built image and access
an interactive shell inside it.

For further information, including how to build the development manually, see
[README.md](README.md).

## Troubleshooting

In order to build the development, you might have to increase the amount of
memory allocated to a running Docker container. We suggest 4GB. For
instructions, see
[here](https://stackoverflow.com/questions/44533319/how-to-assign-more-memory-to-docker-container).
