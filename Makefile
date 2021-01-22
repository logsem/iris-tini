EXTRA_DIR:=extra
COQDOCFLAGS:= \
  --external 'http://ssr2.msr-inria.inria.fr/doc/ssreflect-1.5/' Ssreflect \
  --external 'http://ssr2.msr-inria.inria.fr/doc/mathcomp-1.5/' MathComp \
  --toc --toc-depth 2 --html --interpolate \
  --index indexpage --no-lib-name --parse-comments \
  --with-header $(EXTRA_DIR)/header.html --with-footer $(EXTRA_DIR)/footer.html
export COQDOCFLAGS
DOCKER_IMAGE:=simongregersen/iris-tini

all: Makefile.coq
	cd vendor/modal-weakestpre && $(MAKE)
	+make -f Makefile.coq all

clean: Makefile.coq
	cd vendor/modal-weakestpre && $(MAKE) clean
	+make -f Makefile.coq clean
	rm -f Makefile.coq

html: all
	cd vendor/modal-weakestpre && $(MAKE) html
	rm -fr html
	+make -f Makefile.coq $@
	cp $(EXTRA_DIR)/resources/* html

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

%: Makefile.coq
	+make -f Makefile.coq $@

# Install build-dependencies
build-dep/opam: iris-tini.opam Makefile
	@echo "# Creating build-dep package."
	@mkdir -p build-dep
	@sed <iris-tini.opam -E 's/^(build|install|remove):.*/\1: []/; s/^name: *"(.*)" */name: "\1-builddep"/' >build-dep/opam
	@fgrep builddep build-dep/opam >/dev/null || (echo "sed failed to fix the package name" && exit 1) # sanity check

build-dep: build-dep/opam phony
	@# We want opam to not just instal the build-deps now, but to also keep satisfying these
	@# constraints.  Otherwise, `opam upgrade` may well update some packages to versions
	@# that are incompatible with our build requirements.
	@# To achieve this, we create a fake opam package that has our build-dependencies as
	@# dependencies, but does not actually install anything itself.
	@echo "# Pinning build-dep package." && \
	  if opam --version | grep "^1\." -q; then \
	    BUILD_DEP_PACKAGE="$$(egrep "^name:" build-dep/opam | sed 's/^name: *"\(.*\)" */\1/')" && \
	    opam pin add -k path $(OPAMFLAGS) "$$BUILD_DEP_PACKAGE".dev build-dep && \
	    opam reinstall -j 2 --verbose $(OPAMFLAGS) "$$BUILD_DEP_PACKAGE"; \
	  else \
	    opam install -j 2 --verbose $(OPAMFLAGS) build-dep/; \
	  fi

docker-build:
	docker build \
	  --build-arg=NJOBS=4 \
          --pull \
	  --tag iris-tini \
          --file Dockerfile .

zip-artifact:
	zip -FSr artifact.zip extra html theories vendor _CoqProject doc.html	\
	Dockerfile iris-tini.opam LICENSE Makefile POPL21.md	\
	POPL21.html README.md

# Some files that do *not* need to be forwarded to Makefile.coq
Makefile: ;
_CoqProject: ;
iris-tini.opam: ;

.PHONY: all clean phony
