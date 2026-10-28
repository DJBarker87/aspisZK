# TX2 composition frontier

Stage 1 is PARTIAL. `NCK_Wrapper.second_of_cuts/second_iff` prove the exact
wrapper edge, and `NCK_Stage2Cuts.compose` proves the actual owned top body
from its same-argument cuts. Neither is the requested U00–U14 composition.
The auth/tx2 cut premises in `compose` are explicitly OPEN U16/U15 results;
they must not be advertised as discharged lower bridges.

The consumer is exactly:
```
S2W_D189Wrappers.second (JHe_Natives.second base stage)
  CPH_FixtureData.allocator JHg_World.e2 CPH_Program.verifier data2 slot () =
  ok (.Ok (JHg_World.e2.heap,()))
```
`NCK_Wrapper.second_of_cuts` has this shape after those substitutions, but
its body cut remains unproved. It retains the same proof/checkpoint carrier;
`NCK_Stage2Cuts.compose` never chooses another `selected` or `cp` at tx2.

## Lower-unit audit

No `NCK_Lower_Uxx : Prop` placeholder has been fabricated. The requirement
is to use the lower owner's exact bridge, not a proposition guessed from the
inventory, or a structure concealing whole TX2 acceptance. The table identifies
which exact statement is currently available and what prevents installation.
Absent statements below are missing deliverables, not axioms in new Lean.

| Required name | Owner / available statement | Installation status |
|---|---|---|
| NCK_Lower_U00 | NCB_; `NCB_U00_BRIDGE.md` | enclosing owned allocation/runtime bridge OPEN; partial primitive traces only |
| NCK_Lower_U01 | NBG_/LPi_/LPf_ | per-operation canonical arithmetic laws exist; no single merged full per-unit bridge selected |
| NCK_Lower_U02 | NBG_ | payment/digest helpers; full codec association not installed here |
| NCK_Lower_U03 | NBN_/NBU_; `NBN_U03.conditional` | exact conditional summary in `lean/NBN_U03.lean`; digest encode/decode premises retained; transport into AdapterRw scan unproved |
| NCK_Lower_U04 | NCC_/NCF_; `NCF_EntryContract.op29_exact/op30_exact` | exact active-at-slot Result laws; enclosing account/registry codecs OPEN |
| NCK_Lower_U05 | NBN_/NBU_; `NBN_U05.conditional` | exact conditional validator/encoder summary in `lean/NBN_U05.lean`; raw digest/transfer/withdrawal encode premises retained; AdapterRw carrier installation unproved |
| NCK_Lower_U06 | NBQ_/NCD_ | public dot/finish partial laws; complete same-state numeric association not supplied here |
| NCK_Lower_U07 | NCB_ | full same-execution four-dots/powers bridge OPEN per handoff |
| NCK_Lower_U08 | NCB_/NCD_ | native row/prefix pieces; complete native trace/lifetime bridge OPEN |
| NCK_Lower_U09 | NBY_/NCE_ | no merged complete unit statement in this checkout |
| NCK_Lower_U10 | NCI_ | no merged complete unit statement in this checkout |
| NCK_Lower_U11 | NCI_ | no merged complete unit statement in this checkout |
| NCK_Lower_U12 | NCJ_ | no merged complete unit statement in this checkout |
| NCK_Lower_U13 | NCJ_ | no merged complete unit statement in this checkout |
| NCK_Lower_U14 | NCD_/query continuation | no merged complete native-to-model loop bridge in this checkout |

This does not hold independent top members behind those gaps. Stage 2 continues
with metadata/getters/dispatch and small native cuts. Exact per-unit hypotheses
and caller proofs, U16 reconstruction to byte-identical1880, U15 resume next10
through query22 and relation, and the concrete same-SDK instance remain OPEN.

## Checked domain and same-input additions

- `NCK_SecondBinding.original_inputs`: inverts the SAME accepted model wrapper,
  derives its unchanged heap and identifies the tx2 child's proof suffix with
  original account0 bytes.drop688, length57607, and its checkpoint with original
  account6 bytes, length1768. The scanner's precisely named `ScannerLength`
  law remains a hypothesis. It does not produce acceptance or a cross-TX law.
- `NCK_Admission`: derives seven accounts and successful deferred Clock slot
  from the respective model acceptance equations; no Clock success assumed.
- `NCK_Stage2Shape.fixed_range`: scanner length law transfers to the actual
  top-body selection[688,58295), not an independently chosen suffix.
- `NCK_CommonCuts.compose`: forward value composition through actual resume,
  next10 guard, powers29, batch1, geometry, pending and query22, retaining the
  unreplaced tail on the same returned accumulator/pending. Its premises are
  explicit LOCAL MODEL CUTS, not the missing `NCK_Lower_Uxx` native bridges.

Thus an exact same-input accepted-run interface now exists for lower-lane
integration. The requested forward native-to-cohort theorem, the exact
NCK_Lower_U00–U14 hypotheses and joint accepted2 instance remain OPEN.
