# Corrected association kit re-check

Status: IN PROGRESS. No premise removed, added or changed. S2 and the 100-bit
release target remain open. Headline: `AspisR1.RPx_Deployed.deployed`.

Binding basis: C3-BIN 2026-10-27 23:00 UTC kit-method ruling and KSA inventory.
A2 is kit-relative only until a successful raw-body re-check; no emission
association is inferred from the old theorem names or receipts.

## Stage 0: scope and inputs

Only KSB-prefixed modules and this evidence directory are writable.
Budget: 150 Lean, 0 Kani, 0 Rust. One capped scope at a time; Lean -M7000,
MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64.
Use unchanged S2W runners and coherent SInt2 objects; pin actual Aeneas objects.
Keep `/home/dombarker/project-offloads/codex-cx-kit2-cache-20261027` permanently.

Raw Funs SHA256:
`f4b2d17c061ce7062d64146531788b6448328e656fb6dbd6192f2d61db31a3b5`.
The supplied raw file is not closed over shipped callees. Examples:
`aspis_core.field.QM31.from_le_bytes`, `aspis_core.field.M31.inv`,
`verifier.prepared_claim`, and the circle fallback closure call_once.
These are not Rust std/core library externals. Their absence is distinct
from the iterator/FnMut/from_fn signature mismatch. No replacement is admitted
merely because its name was used in the previous kit.

No shipped source, cfg(kani) harness, other worktree, candidate, wallet or key
changed. No ELF rebuild is triggered. Default/devnet/Pool hashes are inherited,
not newly reproduced. frozen3, RuntimePersistence, ARX_Root, narrowed D188,
security game, failure event, trust inventory and release pins are unchanged.

## Stage 1: exact raw restoration and elaboration obstruction

`KSB_generate.py` reconstructs `KSB_Kit_Funs` from the frozen raw file.
Reversing ONLY the import substitutions and enclosing namespace/section
wrappers recovers every byte of the raw file. `KSB_identity.json` records
all 307 raw declaration spans and identifies all 15 restored edited names.
No shipped-function stand-in is in the new candidate. Types are likewise
byte-exact after import/wrapper reversal; external carriers are explicitly
separate. Library models currently carry no new fidelity credit.

L001 external carriers, L002 raw Types and L003 std/core-only library prefix
pass. L004 WHOLE raw Funs fails: missing shipped callees in addition to the
known iterator ABI mismatch. In particular `QM31.from_le_bytes` is referenced
at raw lines 496/541 and has no declaration in raw Funs; `M31.mul` and
`WideExact.from_limbs` are also missing. The 100-error compiler limit stops
before later missing functions, not a timeout or memory kill. Compiler-generated
sorry diagnostics are rejected; no failed object is accepted as a proof.

The raw translation's dependency boundary is therefore not satisfied by
"raw Funs + Types + std/core externals only". Changing library signatures
cannot define shipped field arithmetic or parser/claim functions. Completing
KIT2 requires additional pinned emitted shipped bodies plus proved carrier/name
associations, or an explicit permitted dependency boundary. No hand-written
shipped stand-in, opaque constant or new premise was introduced to conceal
this obstruction. The whole-kit elaboration item stops here under the
actual-definitions rule; independent kernel-dependency inspection continues.
