# STLC_Ref
Formalization of Subject Reduction in the paper
"Strong Normalisation in λ-calculi with References" [1] 
by Romain Demangeon, Daniel Hirschkoff, and Davide Sangiorgi

In this formalization we only focus on Subject Reduction and Progress.
The main modification to make the proof tractable in this version is the
we remove the hidden dependency from the reduction to the typing judgment,
so we are limited to prove Subject Reduction in the empty context only.

TODO: read / understand / formalize the proof about normalization :D

# Install
```
# install a recent coq, like 8.8 using opam (see [2])

make
```

[1] https://www-apr.lip6.fr/~demangeon/Recherche/impfun2.pdf
[2] https://coq.inria.fr/opam-using.html
