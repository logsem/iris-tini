ARG NJOBS=4
FROM "simongregersen/iris-tini:latest"

LABEL maintainer="gregersen@cs.au.dk"

COPY --chown=coq:coq . /home/coq/

RUN make build-dep

RUN make -j ${NJOBS}

