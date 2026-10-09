# Forward alpha fork cursor focused replay

- Host: `nuc` over Tailscale (`x86_64-unknown-linux-gnu`).
- Toolchain: Lean 4.32.0, commit
  `8c9756b28d64dab099da31a4c09229a9e6a2ef35`, Release.
- Scope: `MemoryHigh=8G`, `MemoryMax=9G`, `MemorySwapMax=0`,
  `RuntimeMaxSec=600`; Lean arguments `-j1 -M8192`.
- Source SHA-256:
  `088051a28ec26a1e8b5cc7d0c2b5271c39734836a8f149318a467abf889906a1`.
- Resulting remote `.olean` SHA-256:
  `a29533d377d3a711b8d7746787969167e5d3d07ddaeb1c747b539002620fc05b`.

The successful command was:

```text
systemd-run --user --scope --quiet \
  -p MemoryHigh=8G -p MemoryMax=9G -p MemorySwapMax=0 \
  -p RuntimeMaxSec=600 \
  /usr/bin/time -v env \
  LEAN_PATH=/home/dombarker/v8w:/home/dombarker/v8w/.lean-union-432:/home/dombarker/v8w/AspisFormal:/home/dombarker/weighted-hensel-repair/.lake/build/lib/lean:/home/dombarker/weighted-hensel-repair/.lake/packages/plausible/.lake/build/lib/lean:/home/dombarker/weighted-hensel-repair/.lake/packages/proofwidgets/.lake/build/lib/lean:/home/dombarker/weighted-hensel-repair/.lake/packages/batteries/.lake/build/lib/lean:/home/dombarker/weighted-hensel-repair/.lake/packages/importGraph/.lake/build/lib/lean:/home/dombarker/weighted-hensel-repair/.lake/packages/mathlib/.lake/build/lib/lean:/home/dombarker/weighted-hensel-repair/.lake/packages/Qq/.lake/build/lib/lean:/home/dombarker/weighted-hensel-repair/.lake/packages/LeanSearchClient/.lake/build/lib/lean:/home/dombarker/weighted-hensel-repair/.lake/packages/aesop/.lake/build/lib/lean:/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean \
  /home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean \
  -j1 -M8192 -o /home/dombarker/v8w/FSV8ForwardAlphaForkCursor.olean \
  /home/dombarker/v8w/FSV8ForwardAlphaForkCursor.lean
```

`forward.retry7.log` records exit status zero, 2.99 seconds wall time,
6,788,424 KiB maximum RSS and zero swaps. Its three `#print axioms` results
are exactly `[propext, Classical.choice, Quot.sound]`.

Earlier logs are retained because they record the dependency-tree and
elaboration repairs rather than silently replacing failed evidence.
