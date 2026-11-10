# PCWX_ handoff (job pc-prov-p5l, phase P5l): PAUSED

Paused on the lead order (owner priority, all Stream C slots to PIN2). No Lean scope and no extraction scope was launched; no host process is running; nothing was changed on the host.

## Where I stopped
Read the P5g inputs (PCWQ_HANDOFF, STATUS, REMAINING, MAP, PINS) and the frozen 4bb3b3f sources for checkpoint, tx1, Accumulator, Prepared, SPLIT and WideExact::to_le_bytes. The domain analysis for X1 is written out in PCWX_REMAINING.json. A background grep for existing Lean-side proved facts about query_loop on research was started and its output was not read.

## Classes
PCWX_STATUS.json gives each of the 24 WAdm keys one class: WAdm_putK EQUALITY_PROVED (P5g), the other 23 CONDITIONAL_ON_BINDING with reason. None moved, because none of the three conditions is discharged.

## Next on resume
1. Find existing proved tx1 facts (grep query_loop/tx1 in research Lean and the L187 closure); write PRVEq domain theorem for candidate.rs:288; show eight_way.rs:113 is outside the release cone.
2. One extraction (cargo --jobs 4, CARGO_BUILD_JOBS=4, --include for aspis_core items WideExact::to_limbs and to_le_bytes), then PRVEq fresh = gate for to_le_bytes versus rawBytes.
3. Cite PCWW_ (P5k) if merged. Then reclassify the 23.

Budget unspent: 20 Lean scopes, 4 extraction scopes.

Target not yet established
