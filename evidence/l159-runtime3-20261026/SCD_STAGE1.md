# Stage 1: canonical-carrier part derived

SCD_Carrier.canonical_stored proves exactly L162's necessary specialization:
(eval H (canon (lift c P))).output.stored = (eval H P).output.stored.
No byte equality, runtime trust or source acceptance is assumed.

stored_iff_observation removes the canonical/semantic-carrier machinery from
the necessary stored association: it is precisely accepted runtime observation
in H -> run.input.stored = (eval H P).output.stored. observation_of_first
proves necessity for any verifier, including the installed source. These are
necessary-condition results, not SCD_Physical.run_eq or premise removal.

SCD_001 exit0, wall4.323218179s, peakRSS5256540KiB, swaps0; source revision
80e0af6281 with exact source hash/snapshot in receipt. All three axiom audits
use only propext, Classical.choice, Quot.sound. -j1 -M7000, 6G/8G/Swap0/64.
Existing hierarchical reservation barrier allowed 8GiB additional against
43352326144 reserved bytes (55GiB safe limit). No retries or dependency builds.
No changes to prior modules or other prefixes. Budget 1/100 Lean, 0/10 Kani.
