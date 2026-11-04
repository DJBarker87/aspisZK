# NFF input repairs and boundaries

All infrastructure is reused unchanged. Own runner repairs only:
- Native public fission needs the canonical module imported at its nested location (K025 codegen failure; K029 succeeds under original harness name).
- Switching from a pairing payload back to the frozen pairing body restored its bytes but left the old own source-pin entry (K037 pre-Kani gate failure). The runner now rehashes every restored frozen source, then applies/pins the payload. Validation remains the same or stricter; K045 is the repaired first actual native run.
- Source fission reverse checks were added inside the capped gate. Native payload, flags, frozen graph and exact KMX patch stay the matching-configuration keys; validation-only source additions are separately pinned.
- L004 was a diagnostic print of a wrongly qualified constant, not a theorem credit. L006–008 are rejected attempts to derive all coefficient-read domains; L009 succeeds. L010–011/L014–015 are rejected proof drafts, repaired at L012/L016. All failed-elaboration sorryAx output is excluded, never an accepted theorem.

canonical::Q::raw is not an independent function in VERTICAL-SLICES slice Q. Its log checks are inline support for the real canonical::Dot::push dependency and cannot earn a raw row. No new out-of-slice row is claimed. External g producers (Prepared/new/powers/prepare) are also outside slice Q; their incoming root obligations remain explicit, never silently asserted as new slice-Q closures.
