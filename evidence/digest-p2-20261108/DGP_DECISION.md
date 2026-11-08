# DGP_: resolution of NNH_ preflight P2 (digestSource)

Target not yet established. Branch codex/cx-digest-p2-20261108 from research
30d37606356. The finding is in NNH_RUN5_PREFLIGHT.md on
codex/cx-integrate-20261107, with the counterexample in NNH_PreflightDigest.lean.
This note decides how the headline `hashv` binder meets the literal op43.

## 1. Exact definitions (quoted)

`S2Z_Oracle.lean`:
```
def RuntimeSyscall (hashv : Parts → Result Digest) (sha256 : Bytes → State) : Prop :=
  ∀ parts digest, hashv parts = ok digest →
    decodeState digest = sha256 (flatten parts)
def P1Realization (sha256 H : Bytes → State) : Prop := ∀ bytes, sha256 bytes = H bytes
```
`S2W_ExtractionBoundary.lean`:
```
structure P1 (sha256 H : Bytes → State) : Prop where
  realization : S2Z.Oracle.P1Realization sha256 H
structure RuntimeSyscall (hashv) (sha256) : Prop where
  returningValue : S2Z.Oracle.RuntimeSyscall hashv sha256
```
`S2W_DigestExtraction.lean`:
```
def digest (hashv : Parts → Result Digest) (self : AdapterRw.SolanaDigest)
    (parts : Parts) : Result Digest := do
  let h ← hashv parts
  toBytes h                                   -- toBytes self = ok self
structure AeneasExtraction (ops) (native1) (native2) (hashv) : Prop where
  ...
  digestSource : ∀ self parts, ops.op43 self parts = digest hashv self parts
```
The headline (`RPx_Deployed.deployed`) takes `(missing : Uninstalled CoreError)`,
`(hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)`, `(sha256 H : Bytes → State)`,
`(p1 : P1 sha256 H)` and `(syscall : RuntimeSyscall hashv sha256)` as independent universal binders.
`extraction` is at `DrvC_Installation.sdk (FIp_Install.configuration indexError
(deployedConfiguration missing indexError reservation) reservation)`.

`IDa_Deployed.lean`:
```
structure Uninstalled (CoreError : Type) where
  adapter : AdapterRw.Ops
  currentBase : AspisR1CurrentCaller.Ops
  stageBase : VTop_Stages.Ops
  reserved : Bool
  query : Port3_NativeQueryBody.Ops
  geometry : Port3_NativeGeometryBody.Ops CoreError
def seed missing reservation := { adapter := missing.adapter, ... }
def deployedConfiguration missing indexError reservation :=
  FIq_Install.configuration indexError (seed missing reservation) reservation
```
`FIq_Install`, `FIp_Install` and `DrvC_Installation.sdk` never set op43
(`grep op43` finds nothing in FIq/FIp, and DrvC only has `digest_call ... := rfl`).
**So op43 is not literal in deployedConfiguration. It is `missing.adapter.op43`.**
NNH_ fixes it through the ruling (s) substitution:
```
-- NNH_Tx2SourceConfiguration
def adapter (base : Ops) (env : RSL.Env) : Ops :=
 {base with op42:=fun _=>.ok (),op43:=fun _ parts=>LIB_Env.hashv env parts,op53:=NNH_EmitModel.code}
-- LIB_Env
def hashv (env : RSL.Env) (parts : Slice (Slice U8)) : Result (Array U8 32#usize) :=
  .ok (nativeKey (env.sha256 (NNC_ResumeEvents.parts parts)))
```
The intended substitution is `missingLit c := NNH_Tx2Configuration.select
(NNH_CorrectConfiguration.residual m0 (envOf c)) (envOf c)`, with `envOf c :=
NNH_HostEnv.environment (sha c) (pda c) (clock c) (reservation c)`. Here `sha c`
is a host Runtime field, and INP_ never defined it.

The trust rows are in design/TRUST-INVENTORY-APPENDIX-DRAFT-20261027.md. Line 80 reads:
`RuntimeSyscall.returningValue | RuntimeSyscall (§3, 2026-10-26) | NAMED-IN-CONTRACT |
... successful hash return only; no termination/totality premise`. Lines 157 and 212 give the
P1 ideal-oracle realization `∀ bytes, sha256 bytes = H bytes` and the
RuntimeSyscall scope "constrains successful returning digests ... without
totality/termination". Line 363 (D188 transport) covers "the external digest with hashv".
NND_RuntimePartial.does_not_imply_total shows that the row does not imply totality.

## 2. Diagnosis

The defect is a missing link between two representations of the same syscall. The
host env reply `sha c` is total. The headline `hashv` binder is partial. In NNH_ run 5
nothing relates them, so the divergent binder is admitted. There is a second fact
(`DGP.fixed_hashv_never_returns`): p1 forces `sha256 = H`. A hashv that does not depend
on the world and satisfies the row at two oracles that differ at an input never returns
at that input. The TAS_TopB `ExecB.Fixed` docstring lists `sha256 p1 hashv syscall` and
`missing` as independent of H, which is consistent only with that never-returning
hashv. Under every sound resolution, the returned digest values (and op43's) vary with H.

## 3. Options

All results are in DGP_DigestMirror.lean (core Lean, exit 0, no sorry/axiom).

**(a) Instantiate hashv at the total adapter.** The three host definitions are:
`hashv c := SqueezeOracleBridge.hashAdapter c.sha256`,
`Runtime.sha c := shaReply c.sha256` (the sha256 of the concatenation), and, per world,
`sha256 := H`, `p1 := ⟨fun _ => rfl⟩`. The resulting proofs:
- `syscall_adapter`: RuntimeSyscall holds as a theorem with no premise.
- `op43_eq_adapter` and `digestSource_adapter`: A0's digestSource holds pointwise.
- `oracle_at_instantiation`: the headline Oracle field follows.

The instantiation is neither vacuous nor weaker. `total_syscall_unique` shows that the
adapter is the ONLY total hashv the row admits. Every run the top consumes returned
(`Runs.ok1/ok2`), so each of its syscalls returned and the existing row
gives reply = sha256(concat) = adapter value. The total model therefore agrees with
the runtime on every consumed run and never invents an acceptance. The adversary `a`
is untouched and the theorem holds at every H (no filter). Owner condition (1) allows
binders to depend on H. No new trust is added. The P1 and RuntimeSyscall rows are
**reclassified, not removed**: they are no longer Lean premises at the top. They justify
reading the actual-run antecedent (Runs/TraceRep at `env c`) as the physical run.
Precedent: ruling (bo) (allocator instantiation) and composition-trust option A.

**(b) `missing.op43 := digest hashv`.** op43 does come from `missing`, so
digestSource holds for every hashv (`b_digestSource`). But A1/A2 then need the
model reply to equal the RSL env reply, and the same divergent binder refutes
that (`b_relocates`). (b) moves the counterexample into A1/A2 and resolves nothing
without a totality premise. A totality premise would be new trust and is physically
false (compute-budget aborts). Rejected.

**(c) Restrict digestSource to the Ok branch.** This is a headline change.
Before: `∀ self parts, ops.op43 self parts = digest hashv self parts`. After (c1):
`∀ self parts d, ops.op43 self parts = ok d → hashv parts = ok d`. The divergent binder
still refutes it (`c1_fails`). After (c2): `∀ self parts d, hashv parts = ok d →
ops.op43 self parts = ok d`. (c2) holds at the divergent binder, but together with
syscall and p1 it does not yield the Oracle field (`c2_insufficient`), so
native_binding/successful_call and the rest of the chain break. (c) needs the owner,
breaks the headline proof and still needs (a)'s env link. Rejected.

## 4. Recommendation

Adopt (a). It is a lead-level instantiation that needs no owner decision. It changes
no contract, number, adversary or H quantifier. Two items are reported to the owner:
the P1/RuntimeSyscall reclassification, and the corrected placement of
`sha256 p1 hashv syscall` and the op43 slot outside `ExecB.Fixed`.

The host statements are in DGP_HostDigest.lean. That file is uncompiled because its
imports exist only on the build host; the same proofs compile in the mirror. They are
`shaReply`, `hashvInst`, `envInst`, `syscall`, `key_digest`, `flatten_parts`,
`op43_value`, `digestSource` and `p1`. A0 is
`⟨fun _ _ _ => rfl, fun _ _ _ _ => rfl, digestSource m0 c.sha256 ...⟩`.

There are two new averaging obligations, needed under ANY resolution (section 2). Both
are stated as Props, not assumed. O1: `NNH_RecordedCharge.recorder` at
`hashvInst sha256` equals the recorder at a fixed `fun _ => .ok d0`. Its mirror is
`program_adapter_fixed`: ART_PartialProgram reads only the status of hashv. O2: the
recorder at missingLit is the same for envs that differ only in sha256 (the account
syntax never reads op43 values). If O2 is false, that is a finding, not a premise.

## 5. Receipt

The mirror was compiled locally with `lean` v4.32.0 on a single file:
exit 0, 0.25 s wall time, 421,937,152 bytes peak RSS, 0 swaps.
File sha256 a8e1bfcc6a5a30cf6c13fe904592e5cb97e82941e250bc5826b58368bc212d22.
The axioms are in DGP_MIRROR_STDOUT.txt: none, propext (c2_insufficient), or
Quot.sound (program lemmas). No host or Lake build, no build-host job.
