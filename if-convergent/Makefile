# Forward most targets to Coq makefile (with some trick to make this phony)
%: Makefile.coq phony
	+@make -f Makefile.coq $@

all: Makefile.coq
	+@make -f Makefile.coq all
.PHONY: all

clean: Makefile.coq
	+@make -f Makefile.coq clean
	find theories $$(test -d tests && echo tests) \( -name "*.d" -o -name "*.vo" -o -name "*.aux" -o -name "*.cache" -o -name "*.glob" -o -name "*.vio" \) -print -delete
	rm -f Makefile.coq
.PHONY: clean

# Create Coq Makefile.
Makefile.coq: _CoqProject Makefile awk.Makefile
	"$(COQBIN)coq_makefile" -f _CoqProject -o Makefile.coq

# Install build-dependencies
build-dep/opam: opam Makefile
	@echo "# Creating build-dep package."
	@mkdir -p build-dep
	@sed <opam -E 's/^(build|install|remove):.*/\1: []/; s/^name: *"(.*)" */name: "\1-builddep"/' >build-dep/opam
	@fgrep builddep build-dep/opam >/dev/null || (echo "sed failed to fix the package name" && exit 1) # sanity check

build-dep: build-dep/opam phony
	@# We want opam to not just instal the build-deps now, but to also keep satisfying these
	@# constraints.  Otherwise, `opam upgrade` may well update some packages to versions
	@# that are incompatible with our build requirements.
	@# To achieve this, we create a fake opam package that has our build-dependencies as
	@# dependencies, but does not actually install anything.
	@# Reinstalling is needed with opam 1 in case the pin already exists, but the builddep
	@# package changed.
	@BUILD_DEP_PACKAGE="$$(egrep "^name:" build-dep/opam | sed 's/^name: *"\(.*\)" */\1/')" && \
	  echo "# Pinning build-dep package." && \
	  opam pin add -k path $(OPAMFLAGS) "$$BUILD_DEP_PACKAGE".dev build-dep && \
	  ((! opam --version | grep "^1\." > /dev/null) || ( \
	    echo "# Reinstalling build-dep package." && \
	    opam reinstall $(OPAMFLAGS) "$$BUILD_DEP_PACKAGE" \
	  ))

# Some files that do *not* need to be forwarded to Makefile.coq
Makefile: ;
_CoqProject: ;
awk.Makefile: ;
opam: ;

# Phony wildcard targets
phony: ;
.PHONY: phony
