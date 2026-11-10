# PCVN_ HANDOFF: phase P3n (callee relations for tx2)

Target not yet established. No ledger row, trust row, RSL, contract or shipped source changed; nothing pushed or merged. Branch codex/pc-prov-p3n-20261110. Lean scopes 16/45, extraction 0/4, one at a time, caps 6G/8G unraised, swap 0, peak RSS 6.8 GiB (the failing op11 kernel-memory scope), verified scopes 2-11 s.

## Difference at a matching configuration
None found. op2: NJC_ClosedCalls.inactive (FIo_Native unrolled emission) and the fresh WideExact.from_le_bytes agree at all inputs.

## Name clash
None. The m1 deployed module recompiled unchanged against the L187 closure (PCVN_L001, exit 0, standard axioms).

## Proved (all exit 0, standard axioms only; see PCVN_STATUS.json)
- op2: PCVN_Op2.op2_frozen (PRVEq_Op2_p5.lean, L009).
- op13: PCVN_Op13.op13_frozen (PRVEq_Op13_p1.lean, L010).
- op17: PCVN_Op17.op17_frozen (PRVEq_Op17_p2.lean, L011/L012), conditional on binding the three aspis-core callees ZERO/ONE/mul to the gate constants, stated in the definitions.
- op3: definitional wrapper of the receipted Op3I_Source parse_shape.
- Composition at the closure's concrete slot values: PRVEq_Tx2Deployed_n1.lean (L016).

## Not done
h18, op5, op6, op9, op10, op11, op19, helpers, derived Clone/PartialEq: PCVN_UNRELATED.json, PCVN_REMAINING.json. op11 install_adopted retired after two failed shapes (L013, L014).
