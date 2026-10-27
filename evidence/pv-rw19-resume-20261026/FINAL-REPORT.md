# pv-rw19 resumed final report

Branch: `codex/cx-prover-rw-20261023`; resume base `bf81d1d222`.
**Target not yet established.** No privacy headline premise or deployment gate
is claimed closed. Work stopped at the **100/100 Lean limit**: 96 passes,
four retained failures. Kani **1/20** charged; its queue stopped at the first
configuration failure, as instructed. Nineteen Kani runs remain unspent.

## V164 before / after

Before: `source_law : ops.op223 = extracted` and
`context_identity : extracted = @ProverRw18ContextCompression.compress _ (PV_CurrentScaleInstall.selected ops)`.

After, for the concrete retained P6 extraction: only
`P_source_p6 : ops.op223 = @ProverRwP6CompressSource.compress _ (PV_CurrentScaleInstall.selected ops)`
remains in `ProverRw19P6Join.callback` / `.dictionaries` and its caller.
`ProverRw19P6ContextIdentity.identity` discharges the context identity; the raw
initializer/iterator/loop identity is also checked for arbitrary slices and
primitive Results. This specializes the arbitrary extracted function to the
owned P6 reference; it does not identify the original whole-helper extraction.
Published rw18/sibling statements are unchanged. V164 remains REDUCED.
The final cb3 search at `80ef4e8e3daa17e1966559bd69fb946eb5eeaf07` found no op223 law.

## V163 before / after

Before: missing the concrete whole-model instance and both full byte/audit
equations in `ProverRw18ContextDataIff.criterion`.

After: canonical successful audit `(16,10,true,true,true,true)` is proved from
the emitted guards. Complete audit correspondence follows from byte
correspondence for the canonical-audit model family, including errors,
failure and divergence. `ProverRw19AssemblyCallerIff.criterion` retains exactly
`P_source_p6`, the unchanged reservation equation, and the byte equation
`P_proof_bytes` reproduced in `MODEL-OBLIGATIONS.md` / `premise-delta.json`.

Independent mathematical serialization and preparation-result functions are
checked; they are not aliases of source output. The deployed caller's
mathematical preparation function is still missing. Neither full fixture byte
equation, nor the general byte equation for arbitrary admitted inputs, is
proved. Therefore V163 remains **OPEN**. Successful original-caller proofs
also have a checked 57,607-byte invariant; this is not byte equality.

## Validation and receipts

Ruling (g) was obeyed: three ten-minute polls, then the restoration flag was
read at 2026-10-26 22:07:43 UTC. No gated host scope or new local Lean compile
ran. Refusals were uncharged and retried after three minutes with fresh IDs.
Next unused Env-J ID: **27829**. Every formal receipt is in numeric files here;
`summary.json` lists all 100 targets and exact metrics, revisions and axiom lines.

| Target / attempt | Exit | Wall | Peak RSS KiB | Swap | Revision |
|---|---:|---:|---:|---:|---|
| P6ContextIdentity / 27789 | 0 | 1.79 s | 4301596 | 0 | 747e3f0dd288744be343c2e553e63b747f62ce11 |
| AssemblyCallerIff / 27825 | 0 | 1.66 s | 4308496 | 0 | c044d029358ba69bacc58bd4b3dbb50e3926b974 + recorded uncommitted SHA |
| FrozenManifest + audit / 27828 | 0 | 1.72 s | 4297632 | 0 | c5c41653d77f1a1ee664b0957c52003c9bbfb9ed |

The final combined audit prints **230 declarations**, only subsets of
`[propext, Classical.choice, Quot.sound]`. The standalone audit at 27826
failed on an absent transitive object before commands ran; its commands were
included in the successful final manifest. Three earlier proof-script errors
were corrected and checked; no failed/sorryAx result is accepted.
This is one cached component replay, not a clean dependency rebuild or a
deployed-release replay. Cache reuse/provenance, import-only corrections and
source hashes are recorded explicitly. Ten legacy transitive object hashes
were first recorded here; they were prior manifest dependencies with sources
unchanged from the resume base. Only Lean import/reference fixes altered
existing proof modules. No shipped Rust/program, launcher, environment or cap
was changed; no ELF build/adoption is claimed.

Kani `gates::step_out_c0a`: exit 1, 0.124 s, 38368 KiB, zero swap, revision
`babcee2df3` (expanded in KANI-STOP.json), axioms N/A. Cargo stopped before
compilation because retained `target` points to a deleted cache. No solver
ran, no unchanged retry occurred, and no checked counterexample was found.
The pinned Charon frontend remains absent at the paths in
`extractor-inventory.json`; no toolchain rebuild was attempted.

## Next deliverable

Prove the actual op223-to-owned-P6 law, then construct the deployed caller's
mathematical preparation/model output and prove full byte equations on both
fixtures and generally; consume the checked audit transport. E1/E2, RunJoin,
L1/L2/L3, client and artifact/deployment linkage remain live obligations.

## Resume commit log

`git log --oneline bf81d1d222..HEAD` before this final evidence commit:

```
c5c41653d7 Keep the full manifest dependency receipt below the shell argument limit
ab5a595d37 Freeze the combined component manifest and full axioms audit after cache recovery
5c38c05c6c Close the selected proof-size invariant and freeze the checked component audit inputs
c044d02935 Validate the P6 context and all inherited rw19 caller and data drafts
747e3f0dd2 Check mathematical data transport and the isolated P6 loop controls
4439eccd9b Isolate generic P6 loop dependencies and draft the raw context identity
f03b98b6ef Check the narrowed front serializer and reference byte-length theorem
c6f17c1f49 Prove guarded assembly length and narrow the shared front serializer import
df18ef2512 Restore focused serialization dependencies with capped compile receipts
1e0566ccd8 Check the original body audit criterion and retain the Kani configuration failure
babcee2df3 Check the canonical audit invariant and complete observation transport
f731589c4f Record the restored gate and first reservation refusal
658cdf4e19 Retain two completed gate polls and explicit assembly error elimination
329549c3ad Keep exact model obligations and the required gate poll procedure
6d81c2d46b Use the symbolic final length guard in the assembly draft
057799e954 Draft the independent guarded mathematical proof assembly adapter
50cb7b2f90 Record the missing pinned frontend and draft preflight
0c2d331c48 Plan full-width iterator to indexed compression transition gates
b896227982 Draft exact canonical audit criteria for the original caller
9ea2c44f0d Resume rw19 under the host restoration gate with budgets retained
```
