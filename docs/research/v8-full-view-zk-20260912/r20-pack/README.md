# Aspis R20 — execution-core candidates

**Target: complete verifier below 1,000,000 CU. Status: NOT achieved or measured
in this packet.** Current pinned R19 source reports 3,279,621 / 3,280,813 CU.
This packet supplies new tested arithmetic implementations and source-directed
integration work, not a claim that a few operation counts prove a 3.28x speedup.

Base: c9315d8b05efb2cdad976bb0f4db3574f1c24577 on
research/v8-r19-channel-fold-20260921. Retain its 699-field protocol, two roots,
quadratic channel proof, T163, sparse G map, 22 queries and security checks.
Do not restart its privacy proof by changing the profile during this experiment.

## What is new

* Beta-weighted gamma preparation: one set of 29 coefficients, full canonical
  decoding, no separate per-slot G multiplication/lerp, unchanged leaf bytes.
* Nine-channel whole-dot accumulation with bounded partial reductions and
  one final field reconstruction; small/empty cases remain special.
* Semantic digest-residual factoring, semantic/G public power-basis sharing,
  and an independently checked scalar adjoint of the grouped G terminal.
* Private canonical two-lane arithmetic and a six-reduction comparison backend.
  Their speed versus the actually staged R19 field routines is UNMEASURED.
* Source inventory and a strict one-million-CU complete-execution evidence gate.

The source still needs integration and SBF measurements. Rust drafts are
self-contained in a no-dependency no_std candidate crate, but were NOT compiled
here. The independent C++ checker was compiled with assertions and undefined-
behavior sanitization, and all listed checks passed. It is not extracted Rust.

## Reproduce local checks

    python3 run_checks.py --sanitize
    python3 tools/verify_manifest.py

The first command compiles in a temporary directory; it does not download
anything. Run `cargo test` / source differential gates in the actual Rust
workspace before integrating. See CODEX_TASK.md, design/MATHEMATICS.md,
design/BUDGET.md and evidence/VERIFICATION.md.

There are no new oracle/hiding/rank assumptions and no omitted checks proposed.
Nevertheless exact source correspondence remains necessary before replacing
any verifier code. No full privacy, soundness or under-1M result is asserted.
