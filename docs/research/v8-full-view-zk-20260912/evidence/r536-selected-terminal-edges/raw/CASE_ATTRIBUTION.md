# Case attribution correction

The earlier loop diagnostic did not print a case label before its assertion.
Its failure must not be attributed to `final256 = e0` or to the first loop
case. The later run is a separate, changed diagnostic: it labels every case
before evaluation and checks only `z=0`, `alpha=0`, `beta=0`, `kappa=tau=1`,
the fixed OOD-derived triple, and actual semantic coins. It covers final256
unit vectors 0, 64, 128, and 192, which become the four terminal coordinates
under three zero-alpha owned-primal folds, plus one deterministic random
vector. That changed diagnostic passed; it does not identify the earlier
unlabelled failing case.
