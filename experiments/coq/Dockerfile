FROM ocaml/opam:debian-stable_ocaml-4.04.1

USER root

RUN apt-get install -y libgtksourceview2.0-dev

USER opam

RUN opam repo add coq-released https://coq.inria.fr/opam/released
RUN opam install coq.8.6 coqide coq-ext-lib coq-mathcomp-ssreflect

# ADD . /coq
# ENV COQPATH /coq
