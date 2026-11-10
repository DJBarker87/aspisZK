# PCWF_ handoff (job pc-prov-p3x)

Target not yet established. No shipped source, ledger row, trust row, RSL or contract changed; no trust row added; nothing pushed or merged.
Frozen source 4bb3b3f. Objects: L187 replay closure by reference. Lean scopes 12 of 35, extraction 2 of 4, one at a time, caps 6G/8G (Lean) and 3G/4G (extraction), swap 0, timeouts unraised, peak RSS 3.0 GiB (Lean), 0.7 GiB (extraction), longest wall 33 s. No difference at a matching configuration was found.

Claims (all exit 0, #print axioms propext/Classical.choice/Quot.sound only, no sorry/axiom/native_decide, heartbeats not raised):
- A, r24_canonical_mul: EQUALITY_DOMAIN (L015, PRVEq_AspisR72Sampler_Funs_A2.lean). On D = all eight limbs < P: r24_canonical_mul l r = ok (some res) and the fresh frozen QM31.mul l r = ok res. Off D: ok none. Its only caller is the gate QM31.mul. It has no standalone frozen function; the frozen counterpart is QM31::mul. SETTLED.
- B, Qm31ArithmeticProbe 7 (reduce_u64, M31.add/sub/mul, CM31.mul, QM31.add/mul): fresh (PCQF_E007, ON) = gate, 13 equalities in all (L001, PRVEq_AspisR1Qm31ArithmeticProbe_Funs_f1.lean). SETTLED. The old COVERED_DIFFERS was a comparison against an OFF (wrapping) emission.
- B, Op3I_Source parse_shape: fresh (PCUJ_E003, ON) = gate for every ParseShapeOps with the externals bound to the ops fields (L005, PRVEq_Op3I_Source_g2.lean). The externals (array-slice eq/ne, HM-D; Iterator::any on slice::Iter, HM-B) are not in the closure's Aeneas library: DEPENDS_ON_LIBRARY_TRUST, not a plain equality. NOT SETTLED unless the lead counts library-trust records as settled.
- C, NGD_SlotRef slot_offset, slot_offset_loop, slot_offset_loop.body: fresh (PCWF_E001, OFF) = gate (L013, PRVEq_NGD_SlotRef_Funs_s2.lean). The callee OFF_NODES (gate literal 28359, frozen Result chain) is related by fresh OFF_NODES = ok gate OFF_NODES, stepwise. SETTLED (3), and the OFF_NODES record itself is covered by the same theorem.
- C, NCX VerifierRegistryEntryV2: ISOMORPHISM with the fresh type (PCWF_E002, ON), callee VerifierEntryStatusV1 (repr(u8) vs none) isomorphic with equal discriminant values (L014, PRVEq_NCX_Reference_Types_n2.lean). The types are distinct Lean declarations; this is not definitional equality. It does not touch the other NCX_Reference records. SETTLED as a type correspondence only.

Failed shapes (recorded in PCWF_ATTEMPTS.jsonl): L002 (symm direction in a hres), L004/L009 (probes), L007/L008 (docstring before open-in; discriminant statement ambiguous), L010/L011 (rfl/decide/norm_num on isize literals: platform-bits blocked; simp with the definitions unfolded works).
Scratch kept: PRVEq_Op3I_Source_g1.lean is the raw generator output (not compiled, superseded by g2), no sorry anywhere.
Remaining: PCWF_REMAINING.json. Receipts: PCWF_L0nn/receipt.json, PCWF_E00n_emitted/*_PINS.json (cargo --jobs 4; identity by class receipt PCWE_E003).

## Hygiene fix after lead review
A1/s1/n1 ran under file-wide maxHeartbeats 1000000 (A1 also 400000/1000000 per theorem): removed. A2/s2/n2 use 200000 throughout with no source change otherwise; recompiled in capped scopes L015, L013, L014, all exit 0, standard axioms only. Lean scopes 15 of 35. Classification: r24 EQUALITY_DOMAIN and NCX type isomorphism count under "other", parse_shape is DEPENDS_ON_LIBRARY_TRUST; of the 12 items only the Qm31 7 and NGD slot_offset 3 are SETTLED (10).
