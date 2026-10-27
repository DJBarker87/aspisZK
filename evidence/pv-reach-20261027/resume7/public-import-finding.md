# Source-closure scanner correction

The inherited resume6 scanner matched only `import`, missing Lean modular `public import`. QM31WordFormulas (EJR blob009f5d04...) publicly imports RawReducerNat; this caused an incomplete project source graph. Affected missing-object failures are retained at39400–39405,39459,39465,39468. The later records name each immediate missing module exactly. No missing declaration or counterexample to a theorem was established by these import failures.

The resume7 resolver now reads public/private/meta import prefixes and all same-line module tokens after removing nested block comments. The corrected closure replaces the earlier source graph; project-closure-before-hidden-import.json retains that earlier inventory. Earlier counts are lower bounds only. All5673 h4 external objects were checked before compiling and remain authoritative. No shared source or object was modified. These focused prerequisite checks are not a release closure replay.

Corrected canonical source graph:1097 project modules,255 under h5. Two newly exposed EJR modules are QM31WordFormulas and QuadraticTowerOperations. No unresolved source authority was found. The195 h5-prerequisite lower bound therefore remains valid; the source graph is not a completed object-closure replay.
