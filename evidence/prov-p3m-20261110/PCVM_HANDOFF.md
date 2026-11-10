# PCVM_ HANDOFF: phase P3m (deployed bindings of the top verifier equalities)

Target not yet established. No ledger row, trust row, RSL, contract or shipped source changed; nothing pushed or merged. Branch codex/pc-prov-p3m-20261110. Lean scopes 9/40 (L001-L009), extraction 0, one at a time, caps 6G/8G unraised, swap 0, peak RSS 5.3 GiB, verified scopes about 10 s.

## Difference at a matching configuration
None. AuS1_Install.base overrides op14/op15 with literals 7783/7751; they equal the emitted OFF_ROUND1/OFF_FOLDED_ROOT (proved).

## Claim (PCVM_L009, exit 0, standard axioms only): PRVEq_Tx2Deployed_m1.lean
For the deployed VTop Ops (RPz7_DrvI_Installation.stage over AuS1_Install.base over the NNH Tx2 stage seed) all Bound fields of PRVEq_VTop_l1 hold except op18 (resume), against externals xdep whose ten callee fields are the deployed fields. So fresh tx2_common/tx2_authenticated at xdep = gate at the deployed Ops, given h18. Proved: eight constants incl. the op14/op15 arithmetic, unwrap32, and the named wrapper of each slot (slot_op*).

## What this is not
The ten callee fields are instantiated by the deployed fields, not related to the frozen callee emissions (organisation, not discharge). Per-callee status, gate item, row status and trust row: PCVM_CALLEES.json, PCVM_UNRELATED.json. op18 retained: PCVM_UNRELATED.json. stage1_owned, stage2_owned, prepare, tx1 not done (deployed Adapter/CurrentCompact Ops need NNH modules absent from the gate LEAN_PATH).

## Failed shapes
L001-L004: importing the un-renamed DrvI chain (four times; retired). L005 import-graph probe showed the RPz7 universe is required. L006/L007 compile errors fixed (AuS1_Install import, implicit args, Usize arithmetic).
