# R198 current byte-body map

The selected freeze byte declarations are staged in [FunsBytes.lean](lean/AspisR197CurrentBytes/FunsBytes.lean) and compile in the pinned focused workspace. The raw generated slice was copied byte-for-byte from `Funs.lean` lines 1460–1511; the mechanical comparison, byte offsets, and source hashes are retained in the evidence bundle.

[R198CurrentBytesBodyMap.lean](lean/AspisV8R19/R198CurrentBytesBodyMap.lean) proves, for every current-field enumeration state and byte vector, that the selected `bytes_loop.body` result maps exactly to `AspisR151QuerySchedule.bytes_loop.body` after converting field elements through `R196.toBefore`. The theorem has no extra premises and preserves iterator/count state, vector writeback, failures, and divergence. The raw declarations and mapper have only the printed foundation axioms; the complete reports and focused run data are in [the evidence manifest](evidence/r198-current-bytes-body-map/manifest.json).

The next obligations are a rank-decrease lemma for actual continuation states, its use in a finite-loop mapper and the complete `bytes` entry, and then the `Vec.extend` and selected gamma-fold chronology. This result does not establish any of those steps, full-freeze execution, or a security property.
