# RSL Revision 4: the TX1:094 public length (ruling (bs))

Target not yet established. This revision changes specifications only. It closes no row and does not prove that any frozen function satisfies its RowSpec.

Frozen source 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387 is unchanged. Ruling (bs) allows one correction, a demonstrable error reported by NNG_ (evidence/tx1-principal-20261111/NNG_HANDOFF.md, NNG_CHECKPOINT_EXTENT094.md). Nothing else was changed: trust rows, runtime assumptions, the security metric, every other Domain and every Ref are as in Revision 3.

Base: research 03c6ca0961b. Branch: codex/cx-rsl-rev4-20261107.

## 1. The error

The CLOSED TX1:186 checkpoint law installed in the library (LIBC_CheckpointDomain.Domain, via LIBC_VTx1B.checkpoint = VLib.checkpoint) requires `a.2.2.2.length = 1880`, where `a.2.2.2` is the public_bytes argument. RowSpec_094 calls `V.checkpoint.run (p, acc2, a.proof, a.public_bytes)` at SAME public_bytes, but its Domain constrained only `obs` and `public`. Frozen tx1 never inspects public_bytes before the checkpoint call, and first_decoded (programs/r1-cost-probe/src/lib.rs) passes it through unchanged, so Revision 3's RowSpec_094 was unprovable for the CLOSED checkpoint law on inputs with any other length.

The length is guaranteed upstream. stage1_owned passes `&public_data` as public_bytes, and the only arm that reaches first_decoded has decoded that same buffer; the frozen decoder returns WrongLength unless `bytes.len() == POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES` (crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs:403). Independently, stage1 snapshots the public account with length1 = length2 = POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES (r1_pool_adapter_owned.rs:453), and snapshot stores Ok bytes only at an admitted length (lines 33-37).

## 2. The fix (same shape as Revision 3 R4)

**TX1:094: own-input clause (P1880) under (bf)(2).**

Before (RSL_TX1_094.lean):
```lean
def Domain (V : VLib) (_a : Args V) (obs : Observer) (pub : V.Public) : Prop :=
  obs = none ∧ V.publicDom pub
```
After:
```lean
/-- Revision 4: the public statement length, POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES. -/
def P1880_LEN : Nat := 1880

def Domain (V : VLib) (a : Args V) (obs : Observer) (pub : V.Public) : Prop :=
  obs = none ∧ V.publicDom pub ∧ a.public_bytes.length = P1880_LEN
```
`Ref` and the `RowSpec_094` text are unchanged.

**TX1:328: caller clause.** first_decoded passes public_bytes unchanged, so the clause is recorded as RSL4-caller:TX1:328:TX1:094:P1880 and RowSpec_328's Domain gains it.

Before (RSL_TX1_328.lean):
```lean
def Domain (V : VLib) (a : Args V) : Prop := V.publicDom a.public_
```
After:
```lean
def Domain (V : VLib) (a : Args V) : Prop :=
  V.publicDom a.public_ ∧ a.public_bytes.length = TX1_094.P1880_LEN
```
`Ref` (which calls 094 through `TX1_094.Domain V x none x.public_`) is unchanged.

**TX1:345: discharge.** The Domain stays `True`. New, after `Domain` (RSL_TX1_345.lean):
```lean
def P1880Discharge (V : VLib) (C : S1Lib V) : Prop :=
  ∀ (b : Bytes) (st : C.Statement), C.decodeStatement b = some st → b.length = STATEMENT_BYTES

theorem p1880_len_eq : TX1_094.P1880_LEN = STATEMENT_BYTES := rfl

theorem p1880_of_decode (V : VLib) (C : S1Lib V) (hD : P1880Discharge V C) (publicData proofData : Bytes)
    (st : C.Statement) (hdec : C.decodeStatement publicData = some st) (n : Nat) :
    (⟨C.semanticPublic st, publicData, slice proofData AFTERSTATE_BYTES PROOF_ACCOUNT_BYTES, n⟩ :
      TX1_328.Args V).public_bytes.length = TX1_094.P1880_LEN
```
`P1880Discharge` is a property of the CLOSED TX1:332 decoder law (line 403 length check), to be proved by the instantiation. It is not a hypothesis of RowSpec_345. `p1880_of_decode` gives (P1880) at the first_decoded call: in `body`, the call is reached only after `RS.ofOption (C.decodeStatement publicData)` returned `st`, and public_bytes is that same `publicData`. Recorded as RSL4-caller:TX1:345:TX1:328:P1880.

On "from the snapshot length": in the RSL model TX1:345 quantifies over arbitrary `OwnedAccount`s (Domain `True`), so the snapshot length established by stage1 is not visible inside 345. The discharge inside 345 therefore goes through the decoder, which enforces the same 1880 on every path that reaches first_decoded. The snapshot fact holds at the only caller, TX1:344, and is recorded in the 345 header and the ledger clause as corroboration. Moving the discharge onto the snapshot would need a new 345 Domain clause discharged by 344, which the ruling does not authorise. If the lead prefers that route it is a one-clause change; I did not make it.

**Rejection examples (all kept).** `TX1_094.rejects_constErr` gains one hypothesis, `hP : a.public_bytes.length = P1880_LEN`, which is needed to enter the Domain; its conclusion is unchanged. `TX1_328.ref_k_det`, `rejects_silentRet` and `ref_admits_abort` compile unchanged (`⟨rfl, hd⟩` now carries both 328 conjuncts). The `TX1_345` and `TX1_344` examples are unchanged. New teeth: `TX1_094.domain_needs_P1880` (no axioms) shows (P1880) is a genuine narrowing.

## 3. Files changed

| File | Change | sha256 |
|---|---|---|
| RSL_TX1_094.lean | header note, `P1880_LEN`, (P1880) in `Domain`, `hP` in `rejects_constErr`, `domain_needs_P1880` | bf8a0a10d2e6a400e3b26118481f3776f2906f5f1dcdb817e707e4d729e9c6fb |
| RSL_TX1_328.lean | header note, (P1880) in `Domain` | 6d0f98a1b348f73e17ec1038c2e53e046b565daba3d5ddcce852991b746d38bf |
| RSL_TX1_345.lean | header note, `P1880Discharge`, `p1880_len_eq`, `p1880_of_decode` | 0c3604546647689575bd879f9579dcab3eface31abb623d1dca8c859307c3adb |
| RSL_Audit.lean | six `#print axioms` lines | 42c6c5df055cd8b16e3e9342e9ec0c214d45bf2be3d422ab85a8aaac15cde922 |
| RSL_LEDGER_CLAUSES.json | RSL4-caller:TX1:328:TX1:094:P1880, RSL4-caller:TX1:345:TX1:328:P1880 (OPEN) | d77af016db1c9ea580d255d0b61dd3a02c19255c991bde6ad45ae3f0df537a02 |
| RSL_INDEX.md | (P1880) entries for 094, 328, 345; Revision 4 pointer | 93fe963b1ff5ed4c476c462f930d0a453daf465f2caca1d2df729f90688ce06d |

All other RSL modules, and TAS_/TFM_/AMN_ sources, are byte-identical to Revision 3.

## 4. Validation

`lake env lean -o` one file at a time, Lean v4.31.0, development Mac. Peak RSS for any file was 0.73 GB, with 0 swaps.
- RSL_COMPILE_REV4.tsv: all 20 RSL modules in Revision 3 order, exit 0 (from a cold `.lake`).
- RSL_AUDIT_OUTPUT_REV4.txt: `RSL_Audit.lean` exit 0. Every Revision 3 axiom line is unchanged. The new lines are: `domain_needs_P1880`, `p1880_len_eq` and `p1880_of_decode` use no axioms; `TX1_094.rejects_constErr`, `TX1_328.ref_k_det` and `rejects_silentRet` use [propext, Quot.sound]. There is no sorry and no axiom declaration.
- RSL_COMPILE_REV4_DEPENDENTS.tsv: TCK_WeakRoot0, TAS_Interfaces, TAS_Top, TFM_TopExact, EVB_EventB, TAS_TopB, AMN_ReturnedPath and AMN_Minimal, staged unmodified in .lake/stage (same sha256 as Revision 3) and compiled against the rev4 oleans, all exit 0. RSL_AXIOMS_REV4_DEPENDENTS.txt contains the same 59 lines as RSL_AXIOMS_REV3_DEPENDENTS.txt (the line order differs only because of compile order).
- Not compiled, as in Revision 3: TAS_TopB_NNE (Aeneas-heavy NNE_ host import) and top-assembly rev2.

## 5. Impact on live jobs

- **NNG_ (TX1 principal).**
  - **094: target changed (weakened).** Domain gains (P1880), so the proof may assume `a.public_bytes.length = 1880` and use it for the length conjunct of the CLOSED checkpoint domain (`LIBC_CheckpointDomain.Domain`, `a.2.2.2.length = 1880`) at the SAME call. This removes the gap in NNG_CHECKPOINT_EXTENT094.md / `NNG_ReturnedExtent094.required`. The other checkpoint-domain conjuncts (driver-established WriterDomain, proof length 57607) are unchanged and still have to be derived at the reached call.
  - **328: target changed.** Domain gains (P1880). At the 094 call the proof must establish `TX1_094.Domain V a none a.public_`, which now includes (P1880); this follows immediately from 328's own Domain because the bytes pass through unchanged.
  - **345: target changed (one more call-site obligation).** RowSpec_345's text and Domain are unchanged, but its Ref calls 328 through `TX1_328.Domain`, which now includes (P1880). The proof discharges it with `p1880_of_decode`, given `P1880Discharge V C` for the concrete S1Lib.
  - 344, 333 and 330: statements unchanged textually. They inherit the discharge through 345's Ref, with no new clause.
- **LIB_ (and LIBC_, which owns the S1Lib instance LIBC_S1).** No VLib field changes. The checkpoint field `VLib.checkpoint = LIBC_VTx1B.checkpoint` stays as it is: its domain's public_bytes conjunct now matches (P1880), which Domain094 supplies at SAME public_bytes. One addition: prove `TX1_345.P1880Discharge` for the concrete `S1Lib` (`LIBC_S1`, `decodeStatement := decode`). LIBC_S1's `decode` already branches on `bytes.val.length = 1880` and maps the other branch to WrongLength (NMT_R2_ReachWrongLength), so this should be a short lemma. Copies of RSL_TX1_094/328/345 in LIB_dependency_inputs (and NNH_dependency_inputs, NND_zero_support) must be refreshed to rev4.
- **NNH_ (integration).** The TAS `Impl`/`Sig`/composition field types (`r094`, `r328`, `r345`) are unchanged in shape and recompile. Any instantiation of `r345 : RowSpec_328 → RowSpec_345` must now supply (P1880) at the 328 call, from `p1880_of_decode` plus the LIBC_S1 `P1880Discharge` lemma. AMN, A1min, A2min, TFM and TAS statements are unchanged. G0 is unchanged.
- **NMX_ (TX2 217/234/233): unaffected.** No TX2 module or TX2 RowSpec changed, and none imports the 094/328/345 Domains.

Target not yet established.
