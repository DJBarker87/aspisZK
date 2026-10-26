# Stage 2 boundary audit: strict raw_join remains open

F3T_JoinBoundary.accepted_eval proves full eval equality from same-H accepted
source, model acceptance and ordered-log equality. collision_or_eval combines
the two collision-alternative conclusions while retaining their alternative.
Neither theorem is a raw join or assumes its desired equality disguised in a
record. They state their log/acceptance premises explicitly.

F3S_Join.accepted_log_eq ranges over a native accepted pair with extraction,
P1/syscall and owner laws. Its SAME-cut continuation additionally needs the
writer/reader headers, protected history and P2Prime. Its conclusion is
Collision OR log equality. F3S_Complete adds conditional model acceptance at
that SAME witness, retaining the five finish owner leaves. It does not yield
an all-byte/all-H strict equality at DrvC's constructed Submission input.

F3T_JoinBoundary.dropping_collision_invalid checks only the pure logical
inference failure: (C OR E) does not imply E. It is NOT an exact-carrier or
installed-source counterexample, and does not prove raw_join is false.
No strict L157 premise was discharged or silently replaced. To proceed requires
joint same-pair non-vacuity, the actual byte/DrvC association and either a proof
of equality also on collisions or an explicitly proved collision-aware endpoint.

F3T_002: F3T_JoinBoundary.lean,exit0,wall1.9416702829767019s,
peakRSS5237132KiB,swap0,revision fb5e66c802 (dirty SHA/snapshot in receipt).
Axiom audits: accepted_eval and collision_or_eval standard three; logical
obstruction none. Same capped command/cache policy as stage1; reservation0.
