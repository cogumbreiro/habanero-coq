#!/bin/bash
check_pkg() {
    opam search -i "$1" | awk '{print $1}' | grep '^'"$1"'$' > /dev/null
}

install_coq() {
  echo "Installing Coq over OPAM..."
  opam repo add coq-released https://coq.inria.fr/opam/released &&
  (opam install coq || true)
}

install_aniceto() {
  if (echo -e "Require Aniceto.List.\n" | coqtop 2>&1 | grep Error); then
    echo "Installing Aniceto..." &&
    opam pin add --dev-repo coq-aniceto https://gitlab.com/cogumbreiro/aniceto-coq.git
  fi
}

(check_pkg coq || install_coq) &&
(check_pkg coq-aniceto || install_aniceto) &&
(test -f Makefile || coq_makefile -f _CoqProject -o Makefile)

