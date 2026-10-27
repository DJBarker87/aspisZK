# Host path loss (2026-10-26)

At op219 extraction, the pinned Charon command exited 127:
`env: /home/dombarker/project-offloads/aspis-r1-r18-tools-20261016/charon-target/release/charon: No such file or directory`.
Receipt: `charon-source-op219-001/collected-receipt.json`.
The pinned Aeneas static executable and shared env-J source/launcher trees
were also absent at read-only inspection. No shared infrastructure was rebuilt,
rewritten, or bypassed. Replacement paths were requested from the lead.

Other retained Charon/Aeneas candidates and older Aeneas object overlays were
found by read-only searches; their equivalence to the pinned toolchain has not
been established and they have not been substituted into accepted source-law receipts.
Local focused Std/BitVec proofs continue in the existing minimal local package.

The full staged-reference Kani gate `kani-gamma-complete-split-001` timed out
at 180s, exit124, without a verdict; it is not rerun unchanged. No own solver
process remained in the post-run process check. No unambiguously attributable
solver temporary file was identified; shared /tmp files were not deleted by guesswork.
Native receipt peak RSS is the `/usr/bin/time -v` reported value, not a
reconstructed aggregate RSS peak. The cgroup memory/swap caps cover descendants.
