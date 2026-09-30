# R141 before-OOD sample bridge report

Both branches of the actual extracted callback `sample` helper now match the
existing exact source-shaped sampler runs in returned value/error and advanced
transcript state.  Challenge exhaustion maps exactly to `Error.Sampler`.

Focused result: exit 0, wall 1.85 seconds, peak RSS 3,704,028 KiB, swap 0.
The exact `before_ood` serializer/chronology, q22 source binding,
admissibility, privacy, and soundness remain open.
