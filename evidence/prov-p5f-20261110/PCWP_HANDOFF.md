# PCWP_ handoff (job pc-prov-p5f, phase P5f)

Target not yet established. No shipped source, ledger row, trust row, RSL or contract changed; nothing pushed or merged. Frozen 4bb3b3f. Objects: L187 replay closure by reference. Lean scopes 25 launched of 30 (L026 not launched), extraction 3 of 6, one at a time, caps 6G/8G and 3G/4G, swap 0, no timeout raised, no kill. Exit-0 Lean scopes: L002 (5.0 s, 2.5 GiB RSS), L011 (7.4 s, 2.6 GiB), L017 (11.4 s, 2.6 GiB), L024 (54.3 s, 2.9 GiB). Extraction E002 (65.5 s, 0.7 GiB) and E003 (71.3 s, 0.7 GiB) exit 0; E001 exit 1 (no opaque on external_linear_lazy). cargo --jobs 4, CARGO_BUILD_JOBS=4, rustc -Zthreads=1, identity by class receipt PCWE_E003.

## Item 1 (condition): from_fn semantics lemma
PRVEq_PCWP_FromFnSem.lean (PCWP_L002, exit 0, standard axioms only). For a stateless Result-valued closure g the gate model FIq_Native.array_from_fn_copy equals length-checked left-to-right evaluation over indices 0..N-1 (array_from_fn_copy_stateless); element i is f(i) when all calls succeed (array_from_fn_copy_elem); the first failing index k fixes the result, fail e (array_from_fn_copy_first_fail) or div (array_from_fn_copy_first_div), independent of g at indices after k. This is a property of the gate model (which is AspisR1.OraclePortStdBuilder.fromFn); it is not a proof about core::array::from_fn itself, which is HM-D.

## Item (a): FIq Native family, from_fn under HM-D
Native04, Native05 and Native07: all 14 OPEN keys proved fresh = gate (PRVEq_RPu_FIq_Native04_n04c.lean L011, Native05_n05_c L017, Native07_n07_c L024; ON configuration, fresh PCWP_E002, original Aeneas 959659a6, P/ZERO/ONE included so constants are definitions). The fresh external core.array.from_fn is instantiated by the HM-D model (inputs/hmd_prelude.lean).
Classes (PCWP_STATUS.json): 12 DEPENDS_ON_LIBRARY_TRUST naming HM-D (one also HM-F), 2 EQUALITY_PROVED (external_local_packed_raw_loop0 and its loop0: closure names no row). Per definition the library externals and the shared boundary externals (aspis_core.field.*, opaque external_linear_lazy, resolved by name to gate constants as in all earlier credits) are listed; see PCWP_CLASSIFICATIONS.json C4/C5 for the two points the lead should confirm.
Not done: Native09, Native10, Native11, Native14, Native01, Native06, NativeExternal: PCWP_L025 (Native11 on fresh PCWP_E003) shows the fresh emission instantiates the core array IntoIter Iterator with fields fold and rev that the gate library structure lacks. Library-model mismatch, no proof attempted; needs the fresh iterator instances reconciled with the gate library.

## Items (b) and (c): not attempted
(b) Post25 low_base_p_digits and ordinary_sample (6 definitions): the fresh closure reaches from_fn (HM-D) and core.slice.Slice.iter_mut, core.iter.adapters.rev.Rev next, Iterator.rev.trait_default, IterMut DoubleEnded (core slice iterator models, HM-B) and a three-component call_mut result; the loop lemma needs those models. Still OPEN. The difference reported by PCWJ (gate two loops versus frozen from_fn) is unchanged.
(c) NativeTypes: not attempted.

## Tool change
PCWP_gen_equalities.py parse_blocks now peels leading import lines (the first declaration of a gate module was silently dropped). Earlier generator-based equalities over modules whose first declaration follows imports without a blank line may have omitted that declaration; recheck if it matters to a credit.

Files: PCWP_STATUS.json, PCWP_REMAINING.json (425), PCWP_ATTEMPTS.jsonl, PCWP_TOOLS.json, PCWP_CLASSIFICATIONS.json, receipts PCWP_Lnnn/receipt.json, PCWP_Ennn_emitted/.
Target not yet established.
