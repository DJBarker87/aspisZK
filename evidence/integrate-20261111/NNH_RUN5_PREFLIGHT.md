# Run 5 preflight: stop at P2

Target not yet established. Branch codex/cx-integrate-20261107.
Binding brief: evidence/int-plan-20261107/INP_NNH_BRIEF.md.

## Results

| Item | Result | Evidence |
|---|---|---|
| S0 | PASS | L707 corrected NNH_ContinuationCombined import |
| P1 | PASS | L708 prints exactly sha256/pda/clock/reservation and proves NNH_PreflightEnv.unique |
| P2 | FAIL (mathematical mismatch; counterexample compiles) | L709 NNH_PreflightDigest |
| P3 | NOT RUN | P2 mandates stop; no slot classified by an unrun rfl probe |
| P4 | NOT RUN | P2 mandates stop; same-recorder rfl not claimed |
| P5 | NOT RUN | P2 mandates stop; no rev4 TX1 Returns replay claimed |

## Exact mismatch

At every pointwise input `parts`, the unchanged literal configuration has

```
(NNH_CorrectConfiguration.sdk missing env err reserve).op43 () parts
  = LIB_Env.hashv env parts
  = .ok (LIB_Env.nativeKey (env.sha256 (NNC_ResumeEvents.parts parts)))
```

A0's `S2W_DigestExtraction.AeneasExtraction.digestSource` instead requires
that complete reply to equal `S2W_DigestExtraction.digest hashv () parts`,
which equals the headline `hashv parts`, including fail/divergence.
`NNH_PreflightDigest.digestSource_at_iff` proves the exact pointwise
obligation is `hashv parts = LIB_Env.hashv env parts`.

The existing `RuntimeSyscall` constrains only returned values:
`hashv parts = .ok digest → decodeState digest = sha256 (flatten parts)`.
It supplies neither return totality nor complete-reply equality.
P1 says `sha256 bytes = H bytes` and also supplies no totality.

The counterexample `divergent := fun _ => .div` satisfies RuntimeSyscall
for EVERY sha256 (`divergent_runtime`) and P1 with H=sha256
(`reflexive_p1`). Yet `digestSource_divergent` proves the two replies unequal
for EVERY missing/env/err/reservation/parts. EnvRep cannot repair this:
it does not constrain the headline hashv's termination. No attack-success,
Root0, Realizes, hash-injectivity or selected-cut premise is used.

Thus the advertised literal host cannot discharge A0 under the stated
binders. No op43 change or new totality premise was installed. The next
concrete deliverable requires resolving the total-library/partial-runtime
reply association while preserving the headline and existing trust boundary.
This is a representation/installation mismatch, not a frozen Rust defect.

## Stop and budget

The explicit S1 P2 instruction says: "If it fails, stop and report the exact
mismatch. Do not change op43 silently." This takes precedence over spending
unused scopes or moving to independent steps. Used3/160 fresh scopes:
S0=1/2, S1=2/10;157 remain unspent. S2 literal host/A0, S3 A2, S4 A1,
S5 NMF_B, S6 HeadlineB, S7 deployed_outer and S8 final consumer were NOT
attempted after that stop. No claim about their impossibility is made.
No new export, raw audit, non-vacuity proof, final manifest or16GiB scope.
No Kani/extraction/shipped-source/key action/push.

Owner condition(4) remains UNPROVED: no literal-host Failure inclusion or
compiled connection to RecordedCharge.bound is delivered in this run.
The requested A1 Err change remains authorized but unimplemented here:
before `∃ pe, model1 ... = .ok (.Err pe)`; after
`¬ ∃ x, model1 ... = .ok (.Ok x)`. No merged NNE module was edited.

## Focused receipts

All three scopes: MemoryHigh6G,MemoryMax8G,swap0,TasksMax64,Lean-M7000;
admission allowed=true/exit0, host disk>=40GB, one scope at a time.
Sources/dependency hashes and exact revision are in each receipt.

| Attempt/target | Exit | Wall(s) | Peak RSS(KiB) | Swap | Revision |
|---|---|---|---|---|---|
| L707 NNH_ContinuationCombined |0|11.528838|6517428|0|30d37606356|
| L708 NNH_PreflightEnv |0|4.479405|5676800|0|b41616f97ec|
| L709 NNH_PreflightDigest |0|5.197199|6658612|0|b41616f97ec|

L708 unique: [propext]. L709 reflexive_p1: no axioms; divergent_runtime,
digestSource_at_iff,digestSource_divergent:
[propext,Classical.choice,Quot.sound]. Full lines in stdout.log/receipt.json.
L707 is an import/#check, not a new top theorem; no new raw ax2 audit claimed.
