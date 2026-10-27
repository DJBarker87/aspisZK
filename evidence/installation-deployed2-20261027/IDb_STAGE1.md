# IDb inventory checkpoint

Evidence job only. No adoption, ledger/contract/root edit, or release claim.
Starting revision: 223ab94556b28ef0ecf8ac32a45ecaf2938803b0.
Actual branch: codex/cx-installation-deployed2-20261027 (prompt label says 20261026).

Read the governing AGENTS security/proof discipline, common/local Lean rules,
S2 ownership handoff/plan/diagnosis/route-B ruling, S2LeadInterface, owner
amendments, IDa decision/configuration/recount/source and SInt2 handoff.
Historical paths absent at repository root were read under
`docs/research/100bit-spend-path-20261013/`.

Six residual inputs are being audited by their actual installation path:

- adapter: AdapterRw.Ops; CPP selects clone/key equality; DrvI installs callers.
  Other dictionary slots remain seed inputs, including digest op43.
- currentBase: AspisR1CurrentCaller.Ops; Uni and NativeBuffers/Claims select
  children, but no seed-free dictionary is supplied by these constructors.
- stageBase: VTop_Stages.Ops; Port1 installs library/constants; AuS1, Tx2N,
  Op5T and Tx2I install children. Some source body callbacks remain seed inputs.
- reserved: Bool passed into Port3_Initial.constructor, pending and checkpoint
  reader; it represents allocation outcome, not a release constant.
- query: all 23 slots are overwritten jointly by SAQ_Decoder, FIp and the
  Port4C_RowStd/Port5Q1_QueryPorts/Port3_QueryStage consumer installation.
  A seed-free effective dictionary can therefore be constructed without
  arbitrary defaults. Kernel independence checks pending.
- geometry: SAQ_Constructor fixes arithmetic/domain; GeometryTerminal fills
  std, prefix and collector. Its prefixCall closes over op9/op7, already fixed
  by SAQ. A seed-free effective dictionary can be constructed. Checks pending.

New modules use IDb_ only. At most40 Lean attempts, one capped scope at a time,
existing host reservation/runner, no package replay. No prover has run yet.
