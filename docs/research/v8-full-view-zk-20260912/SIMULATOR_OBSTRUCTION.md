# Current simulator obstruction

No efficient witness-free full-view simulator exists for the current q22 path
at the intended privacy level. The decisive same-public attack is:

1. Use the same commitment in both input slots and switch only
   `selected_second`. The public statement and snapshot remain identical.
2. The actual encoder changes only rows 913 and 1017. Fibres 4 and 6 expose
   row 913 through the retained eight-coordinate separator, yielding
   `1959911333` versus `303025598` in M31.
3. The fixed-pair event has exact probability `11/1636171776` for uniform
   distinct q22 sampling (about 2^-27.15), so this is a concrete public-view
   distinguishing event, not merely a proof-route obstruction.

The earlier obstruction evidence remains relevant context:

1. The straightforward universal affine sampler would need every allowed
   offset at each chronological disclosure to lie in the remaining conditioned
   mask image.
2. Universal raw-opening surjectivity is false for the fixed q22 schedule
   `0..21`: the retained certificate supplies a nonzero functional that
   annihilates all reconstructed column-3 mask directions while detecting the
   removed row-1014 direction.
3. The reconstructed q22 host prover does not apply the repository's separate
   q18 publication gate, so the simulator cannot justify deleting this
   schedule from the real distribution.
4. A focused actual-encoder probe shows that this obstruction is structured:
   five consecutive schedules had rank 56 and exposed row 1014, while 32
   deterministic pseudorandom distinct schedules had rank 88 and contained
   its displacement. The bounded sample supplies no upper bound on all bad
   schedules and cannot populate `epsilon_algebraic_bad`.
5. On valid positive-transfer traces the functional is exactly
   `L(semantic column 3) + 170822063 / (recipient_value * change_value)`.
   Three distinct deterministic mask seeds gave the same final value for each
   of seven valid amount splits, while the pre-overwrite functional changed
   with the seed. This establishes a real witness-shaped semantic quantity,
   not merely an arbitrary cell offset.
6. The same-public pair now resolves the prior uncertainty: the quantity is
   witness-dependent even when all public statement fields are fixed.
7. Earlier semantic, point/OOD, D, helper and commitment disclosures have not
   yet been assembled into source-derived M31 conditional maps. Solving the raw
   C1 marginal alone would not preserve those earlier observations.

The next valid simulator step must either derive or sample the observed
quantity efficiently from the public view, or construct a same-public valid
witness-difference source and test its image in the joint conditioned map. A
separately reviewed q22 publication gate with a source-linked abort/retry law
is a possible later repair, not a substitute for this diagnosis. Until one of
those routes closes, a purported simulator would need the witness, an unproved
favorable-schedule assumption, or retroactive oracle/mask changes. Each is
outside the target definition.

This is a concrete failure of the intended full-view adaptive-ZK claim for the
current q22 bytes. See `SAME_PUBLIC_ATTACK.md` for the repair boundary.
