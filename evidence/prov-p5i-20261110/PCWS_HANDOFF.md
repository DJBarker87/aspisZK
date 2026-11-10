# PCWS_ handoff (job pc-prov-p5i, phase P5i)

Target not yet established. No shipped source, ledger row, trust row, RSL or contract changed; no trust row added; nothing pushed or merged. Frozen 4bb3b3f. Objects: L187 replay closure by reference. Lean scopes 12 of 30, extraction scopes 8 of 8, one at a time, caps 6G/8G and 3G/4G, swap 0, no timeout raised. Peak RSS 2.7 GiB (Lean), 3.1 GiB (extraction, PCWS_E006); no raised heartbeats.

Set: PCWS_SET.json (OPEN in PCXL_COUNTS_CLASSES.json at research 9fb1e206d7d minus siblings and CANNOT_EXTRACT modules): NJS_Extract.Funs 15, AspisR1TerminalDecoder.Funs 10, AspisR1DecodeKFullV10.Funs 4, NGT_Emitted 4; amended with NID_ResumeEmissionTypes 3 and NID_ResumeEmissionFuns 2 (existing pinned emission) once extraction ran out.

Settled (PCWS_STATUS.json has theorem names and files):
- NJS_Extract.Funs, 15 of 15 (PRVEq_NJS_Extract_Funs_s4.lean, PCWS_L004, exit 0, 48 theorems, standard axioms): fresh OFF emission (PCWS_E001 LLBC, extended Aeneas PCWS_E003) = gate after parametrizing the fresh emission as the gate is (PCWS_param.py). 4 EQUALITY_PROVED (from, same_batch_index, same_batch_leaf, batch_keys_loop.body with the ShrAmt bridge), 10 CONDITIONAL_ON_BINDING (batch_leaf, slot, eight canonical_scan definitions), 1 DEPENDS_ON_LIBRARY_TRUST (parse_shape: HM-D, HM-B).
- NID_ResumeEmissionTypes, 3 of 3 TYPE_ISOMORPHISM (PRVEq_NID_ResumeEmissionTypes_s6.lean, PCWS_L012, exit 0).

Not settled: TerminalDecoder 10 CANNOT_EXTRACT (Aeneas original: 180 s timeout twice; extended: uncaught exception), DecodeKFull decode_k family 3 CANNOT_EXTRACT (Aeneas Internal error at r1_wire.rs 158-165 with both tools) and decode_k_value NO_FROZEN_COUNTERPART, NGT_Emitted 4 not attempted, NID_ResumeEmissionFuns 2 OPEN. PCWS_REMAINING.json.

Next: second tool pair on TerminalDecoder (one Charon+Aeneas scope), NGT_Emitted frozen counterpart search, NID Funs variable-to-fresh map (25 variables).
Failed shapes and the wasted scope PCWS_L002: PCWS_CLASSIFICATIONS.json PCWS-C7, PCWS_ATTEMPTS.jsonl.

Target not yet established.
