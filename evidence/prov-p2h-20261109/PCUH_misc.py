#!/usr/bin/env python3
import json,sys,hashlib,collections
from pathlib import Path
sys.dont_write_bytecode=True
H=Path(__file__).resolve().parent
sha=lambda f: hashlib.sha256((H/f).read_bytes()).hexdigest()
tools=dict(schema='PCUH_TOOLS/1',note='P2h ran 0 extraction scopes; the fresh emissions are P1g/P1d outputs (tool per run below). Lean scopes: the ledger30 gate environment, one scope at a time, caps 6G/8G swap 0, 180 s, -j1 -M7000 -DElab.async=false.',
  lean=dict(toolchain='leanprover--lean4---v4.32.0 (GATE_T in PCUH_run.py)',gate_export='codex-cx-ledger8-cache-20261104/NNN_20261111/NNN_exports with LEAN_PATH list from evidence/ledger30-20261111/NNN_PATHS.json',launcher='PCUH_run.py / PCUH_run_host.py (copies of PCVD_run*.py with prefix and workspace renamed; admission host<6, Stream C<2, disk>=40GB, reservation barrier)'),
  aeneas=dict(original='959659a6aafc6a6a975b4dc67ee9d779a269b988bd44b3b31a77cf023b1709e3 (rebuilt original, rev b59d5188): PCQD_E003 (AdapterReconstruct), PCQD_E013 (compact/S1), PCQE_E001 (r0.transport.order)',
              extended='c0cf4fccb0879db4ce342da991f6215732a19fc01345b9eec84e632f4673b958 (aeneas-b59d5188-extended): all other PCQD_ runs used here (E010,E011,E018,E024,E027,E028,E034,E035,E036)',
              charon='daad69bea1114042a2d2fbd3dfde99922b152d4f57023bf8edb83e5a6f336af8'),
  overflow_checks='ON in every fresh emission used (PCQD-C2; the gate module text was NOT used to re-derive the fresh configuration, but each definition is scanned for wrapping_ operators: PCUH_EQ_STATUS gate_requires_wrapping_ops)',
  generator=dict(file='PCUH_gen_equalities.py (copy of PCUG_gen_equalities.py + --preamble, --fresh-prelude, --given, --extra-import)',sha256=sha('PCUH_gen_equalities.py'),driver='PCUH_gen.py, PCUH_plan.py, PCUH_ingest.py, PCUH_bundle.py'),
  hand_written_inputs={f:sha('inputs/'+f) for f in ['R72_preamble.lean','R72_given.json','NFN_prelude.lean','NFN_given.json','NFN_p2_given.json','S1_given.json']},
  generic_lemmas=dict(file='PRVH_WrapAdd.lean',sha256=sha('PRVH_WrapAdd.lean'),theorems=['PRVH.usize_add_one_wrap','PRVH.usize_add_one_of_lt','PRVH.usize_shr9','PRVH.update_ok_lt'],scope='PCUH_L029 (final), axioms propext/Classical.choice/Quot.sound (update_ok_lt: propext)'))
json.dump(tools,open(H/'PCUH_TOOLS.json','w'),indent=1)
hand=dict(schema='PCUH_HAND_MODELS/1',note='Record only; no trust row is added or proposed. These are the hand-written gate structures that block a fresh = gate equality, and the instantiations used by this job.',
 hand_models=[
  dict(module='AdapterRwModel',name='AdapterRw.Ops (boundary record)',effect='gate functions first_decoded, observer, data_len, require_verifier_checkpoint, Insts.* take `ops`; fresh uses SDK/cross-crate externals as axioms; 9 comparisons not made (HAND_ADAPTED)'),
  dict(module='Port3_NativeGeometryBody',name='Ops (callbacks for field/domain operations)',effect='23 for_range definitions parametric in Ops, carrier types CM31/M31/r0.Error/Point/QueryGeometry differ from the fresh ones'),
  dict(module='Port4C_NativePrefix',name='Leaves',effect='batch_prefix_products(_loop(.body)) parametric in Leaves'),
  dict(module='Port5Q2_ReaderWeights',name='CheckpointBytes4Sections.ReadK + IterMut model',effect='weights, weights_loop parametric; carrier types differ'),
  dict(module='S1NativeCompactModelV1',name='Ops (compact codec) and hand-written constants r1_wire.POINTS : Result Usize := ok 3#usize',effect='expand_semantic(_loop(.body)) parametric in Ops and fresh does not elaborate (ChunksExactMut externals); POINTS/CLAIMS compared in the lifted form `ok fresh = gate`'),
  dict(module='AspisR72Sampler.Funs',name='r23_product_u32_bounded, r24_canonical_mul (+ PP, closure)',effect='gate-only helpers with no frozen counterpart; behaviour proved in P3b (r23_gate reused here), not equated')],
 instantiations_recorded=[
  dict(where='PRVEq_NFN_ExtractedGeometry(_p2): fresh-namespace definitions aspis_core.field.M31.ZERO/ONE := ok <gate value> (inputs/NFN_prelude.lean)',effect='external `Result M31` axiom of FunsExternal_Template instantiated; used by fast_domain.line_node; value now verified against the constant\'s own transparent fresh definition (PRVEq_const_bind.lean PRVEq.const.M31_ONE, PCUH_L037)'),
  dict(where='external callees of the fresh closures (cross-crate M31.mul/sub/double, CM31.mul, FibreIndex.get, ...) resolve by name to the gate constants through the opened gate namespace',effect='name-bound (as in P2g); the compile is the check; applies to NFN fibre_point/line_node/table_value')])
json.dump(hand,open(H/'PCUH_HAND_MODELS.json','w'),indent=1)
fs=[]
for line in open(H/'PCUH_ATTEMPTS.jsonl'):
    x=json.loads(line)
    if x.get('event')=='result': fs.append(dict(attempt=x['attempt'],module=x.get('module'),exit=x.get('exit_status'),wall=round(x.get('wall_seconds',0),1),rss_kib=x.get('peak_rss_kib')))
json.dump(fs,open(H/'PCUH_SCOPE_SUMMARY.json','w'),indent=1)
cls=dict(schema='PCUH_CLASSIFICATIONS/1',entries=[
 dict(id='PCUH-C1',topic='r0.transport.order',classification='SOURCE_SHAPE (configuration): fresh PCQE_E001 uses checked `j + 1`, `r + 1`; gate FIo_Native uses `wrapping_add`',
      result='EQUALITY_PROVED as functions on all inputs; no caller domain needed: the gate body is the fresh body because overflow cannot occur (r < PIVOT = 1023 guard; j+1 follows Array.update out j i, whose success certifies j < 1024). order is a constant function (no arguments). No reachable disagreement.',
      also='constants PADS, PIVOT, PAD_ROWS: fresh transparent definitions proved equal to the gate constants (unfold; rfl), so no CONDITIONAL_ON_BINDING',
      config_note='fresh ON vs gate wrapping on plain operators. Under the ruling (wrong basis counts OPEN) a plain ON=OFF match would not count; here the equation itself is proved across the two configurations, which is the stronger statement. R22 (checked-to-wrapping) is not discharged by this: it applies only to these 8 definitions.'),
 dict(id='PCUH-C2',topic='which fresh emissions were compared',rule='every FRESH_PRESENT_PCQD entry of PCQD_COVERAGE whose gate source is available; one generator pass per (gate module, emission directory, kind) in PCUH_PLAN.json; ALREADY_COVERED, NOT_OBTAINED and NO_FROZEN_COUNTERPART entries are not re-run (reported in PCUH_COVERAGE_RESULT.json)'),
 dict(id='PCUH-C3',topic='hand-adapted (parametric) gate models',rule='when the gate definition takes a hand-written record (Ops, Leaves, ReadK) and its carriers differ from the fresh ones, fresh = gate has no meaning as an equation; recorded HAND_ADAPTED, not OPEN-failed, not credited'),
 dict(id='PCUH-C4',topic='config mismatch',rule='gate body with wrapping_ operators vs fresh checked, no overflow-freedom argument found: CONFIG_MISMATCH, OPEN. NJA_CountBody (6) and the NFN closure/for_range family (11) are in this class. Counterexample candidates (not claimed reachable): NFN closure_4.closure call_mut computes `5#usize * i + tupled_args`; for i >= 2^64/5 the fresh body fails with an arithmetic-overflow error where the gate wraps. The caller domain of i (query index in QueryGeometry.for_range) was not proved bounded in this job.'),
 dict(id='PCUH-C5',topic='given blocks',rule='R72 M31.mul, CM31.mul, CM31.square, QM31.mul reuse the P3b proofs (PRVEq_AspisR72Sampler_Funs_P3.lean) verbatim: the fresh text of those definitions in PCQD_E024 is identical to PCQF_aspis_core_field_a (checked in PCUH session by normalized-text comparison for M31.mul, CM31.mul, CM31.square, QM31.mul, QM31.square, reduce_u64, mul_by_r, CM31.add/sub/double), so the proofs apply unchanged. The block is compiled in PCUH_L032 with the new emission. NFN fibre_point/line_node and batch_prefix_products_loop(.body) and S1 POINTS/CLAIMS are P2h hand-written blocks.'),
 dict(id='PCUH-C6',topic='constant binding upgrade (item 4)',rule='The constants\' own transparent fresh definitions (PCQF_E007: M31.ZERO/ONE, QM31.ZERO/ONE) equal the gate constants (limbwise for QM31): PRVEq_const_bind.lean, PCUH_L035/L037. P3d records that used QM31.ZERO/ONE or FIq_Native M31.ONE (11) and the NFN line_node pass are upgraded to EQUALITY_PROVED with `binding_upgrade`; the cross-crate link external axiom = transparent value remains a property of the Aeneas encoding of constants and is recorded. Not upgraded: Native07 selected_claim (STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS, no transparent emission located), Native13 COPY_PATTERNS (retired shape), parametric-transport rows.'),
 dict(id='PCUH-C7',topic='failed shapes',rule='PCUH_L002-L009: PRVH_WrapAdd lemma development (identifier/arith lemma names); PCUH_L012/L013: r0.transport.order first drafts (abbrev G := namespace is not a term; apply on a bind whose first argument differs); PCUH_L015-L018 probes, L025 (CM31 proofs lacked r23_gate), L027 (docstring before set_option; fibre_point table equalities missing; line_node kernel excessive memory in the stage-2 `try rfl` fallback, replaced by explicit `simp only [fibre_point, bind_tc_ok]`). None repeated unchanged. Two shapes (S1 stage-1 rfl, S2 delta+simp+rfl) both timed out at 200000 heartbeats for AspisR72Sampler circle.secure_ood_circle_point_from_parameter: retired.'),
 dict(id='PCUH-C8',topic='scratch files with sorry',rule='PRVEq_probe1.lean and PRVEq_probe3.lean contained sorry; deleted from the tree, and the source copies in PCUH_L001/L022/L023 were removed. They carry no credit. PRVEq_probe2.lean/probe4.lean have no sorry.'),
 dict(id='PCUH-C9',topic='NJA_CountBody loop0_loop0_loop0.body',rule='present in the gate and the fresh emission but not parsed as a common declaration by the generator (6 of 7 compared); config mismatch class anyway'),
])
json.dump(cls,open(H/'PCUH_CLASSIFICATIONS.json','w'),indent=1)
print(len(fs),'scopes')
