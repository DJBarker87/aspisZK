#!/usr/bin/env python3
"""PCVB_deliver.py: writes PCVB_CLASSIFICATION.json, PCVB_STATUS.json, PCVB_REMAINING.json, PCVB_HAND_MODELS.json, PCVB_TOOLS.json."""
import json,hashlib,glob,collections
from pathlib import Path
E=Path(__file__).resolve().parent;R=E.parent
f3=json.load(open(R/'prov-p2f-20261109/PCUF_FOR_P3.json'))['items']
nf=json.load(open(R/'prov-p6s-20261109/PCXA_NONFROZEN.json'))['modules']
items=[i for i in f3 if i['status'] in ('FAILED','CONFIG_MISMATCH')]
RESOLVED={ # definition -> theorem
 'AspisR72Sampler.field.M31.mul':'PRVEq.AspisR72Sampler.Funs.field.M31.mul','AspisR72Sampler.field.CM31.mul':'PRVEq.AspisR72Sampler.Funs.field.CM31.mul',
 'AspisR72Sampler.field.CM31.square':'PRVEq.AspisR72Sampler.Funs.field.CM31.square','AspisR72Sampler.field.QM31.mul':'PRVEq.AspisR72Sampler.Funs.field.QM31.mul',
 'AspisR72Sampler.field.QM31.square':'PRVEq.AspisR72Sampler.Funs.field.QM31.square',
 'AspisR65Field.field.M31.mul':'PRVEq.AspisV8R19.ComplexFieldSlice.field.M31.mul','AspisR64Field.field.M31.mul':'PRVEq.AspisV8R19.GuardedFieldSlice.aspis_core.field.M31.mul',
 'AspisR66Field.field.M31.mul':'PRVEq.AspisV8R19.QuarticFieldSlice.field.M31.mul'}
FILE={'AspisR72Sampler.Funs':'PRVEq_AspisR72Sampler_Funs_P3.lean:PCVB_L040','AspisV8R19.ComplexFieldSlice':'PRVEq_AspisV8R19_ComplexFieldSlice_P3.lean:PCVB_L042',
      'AspisV8R19.GuardedFieldSlice':'PRVEq_AspisV8R19_GuardedFieldSlice_P3.lean:PCVB_L043','AspisV8R19.QuarticFieldSlice':'PRVEq_AspisV8R19_QuarticFieldSlice_P3.lean:PCVB_L041'}
def classify(i):
    d=i['definition'];m=i['module'];st=i['status'];err=i.get('error') or '';fc=i.get('failure_class')
    if d in RESOLVED: return ('SEMANTIC','RESOLVED_P3B','fresh = gate proved on ALL inputs (no caller domain needed): see PCVB_STATUS.json')
    if st=='CONFIG_MISMATCH':
        return ('CONFIG_MISMATCH','OPEN_CONFIG_MISMATCH','gate module text uses wrapping_* (overflow-OFF); fresh emission with checked arithmetic (ON). '+('P2a holds a compiling OFF theorem (PCQ_E415 OFF emission, PCUA_L006) for this definition; the consolidated status takes it.' if any(k in d for k in ['canonical.reduce','Dot.finish','EbyKDot']) else 'No OFF emission of the matching configuration exists for this definition (reduce_u64) or the OFF emission fails on the library wrapping_shr shift type (transport row_loop*); recorded per the brief, not proved.')+' Deployed wrapping is owned by R22.')
    if 'compact.OFF_' in d or 'compact.LOGICAL' in d: return ('HAND_ADAPTED','OPEN_HAND_ADAPTED','gate constant is parameterised by an Ops instance (gate: `def compact.X (ops : Ops) : Result Usize := ops.opNN`) while the fresh constant is a closed literal/HEADER-derived value; equality needs an axiom about the Ops fields, which is a modelling assumption, not provable. Not proved.')
    if 'timeout' in err: return ('SOURCE_SHAPE','OPEN_HEARTBEAT','`isDefEq`/`whnf` heartbeat timeout at 200000 (never raised); body too large for definitional unfolding; needs a stepwise (step*/spec) proof of the callee chain.')
    if d.endswith('reduce_u62') or d.endswith('qm31_pack_base4'): return ('NOMINAL','OPEN_NOMINAL','bodies are text-identical; the equality fails because the gate module has no `field.reduce_u64` constant matching the fresh callee (P2f emitted no callee theorem), i.e. a callee-binding gap, not a semantic difference.')
    if m=='AspisR1TerminalDecoder.Funs' and 'digest_is_canonical' in d and 'forest_accounts' in d: return ('SEMANTIC','OPEN_SEMANTIC','loop-return refinement (P3a TerminalDecoder: holds under H_P; P2f discharged H_P for TD_HP). Type mismatch between fresh `Result U32` P and gate constant; PCUF_ALL_STATUS records EQUALITY_DOMAIN for pair_forest_accounts.digest_is_canonical. Caller domains not re-examined in P3b.')
    if fc=='transport-needed': return ('SOURCE_SHAPE','OPEN_INSTANCE_BOUNDARY','fresh declaration (or callee) does not elaborate against the gate instance/boundary: the gate abstracts an external (heap/ChunksExactMut/slice/Ops instance); needs a transport lemma, not attempted in P3b.')
    return ('SEMANTIC','OPEN_SEMANTIC','unsolved goals after delta/unfold; difference not yet characterised; caller domain not examined in P3b.')
cl=[]
for i in items:
    c,s,note=classify(i)
    cl.append({'module':i['module'],'definition':i['definition'],'p2f_status':i['status'],'class':c,'p3b_status':s,'note':note,'configuration':i.get('configuration'),
               'gate_configuration_by_text':i.get('gate_configuration_by_text'),'gate_module_flagged_nonfrozen_by_PCXA':i['module'] in nf,
               'source_drift':('gate module extracted from non-frozen source (PCXA_NONFROZEN.json); '+('blob a47a9996aa63 for AspisR72Sampler' if i['module']=='AspisR72Sampler.Funs' else 'blob not identified') if i['module'] in nf else None),
               'theorem':RESOLVED.get(i['definition']),'file_and_receipt':FILE.get(i['module']) if i['definition'] in RESOLVED else None})
tot=collections.Counter(x['p3b_status'] for x in cl)
classification={'schema':'PCVB_CLASSIFICATION/1','target_established':False,'n_items':len(cl),'counts_by_p3b_status':dict(tot),'counts_by_class':dict(collections.Counter(x['class'] for x in cl)),
 'principles':'NOMINAL = naming/binding gap with identical semantics; SOURCE_SHAPE = fresh and gate differ in structure (instances, boundaries, size) but not intended semantics; SEMANTIC = body differs; HAND_ADAPTED = gate is a hand model; CONFIG_MISMATCH = checked vs wrapping.',
 'findings_for_lead':[
  'M31.mul: the FULL equality fresh(4bb3b3f)=gate holds on ALL inputs for AspisR72Sampler, AspisR64Field, AspisR65Field, AspisR66Field. The gate fast path is taken only when both operands are < P, and for those the product is <= (P-1)^2 < P^2. No caller canonicality is needed, so no reachable-caller question arises for this family.',
  'Counterexample to the unguarded fast-path arithmetic (why the guards matter): x = 2^62 - 1 = P^2 + 2P gives first fold 2P, so the fast path returns P (non-canonical) while reduce_u64 returns 0. The fast path equals reduce_u64 only for products <= P^2 (proved with the guard-derived bound a*b <= (P-1)^2).',
  'The eight definitions in PCUF_FOR_P3 did NOT all follow by congruence from M31.mul: R72 CM31.mul/CM31.square also use the gate-only helper r23_product_u32_bounded (proved equal to the plain u64 product), and R72 QM31.mul has a gate-only fast path r24_canonical_mul (absent from frozen field.rs) that is a different algorithm (direct 8-limb formula with wrapping u64 arithmetic). QM31.mul fresh = gate was proved on all inputs: non-canonical -> none -> same Karatsuba chain; canonical -> some result proved equal limb by limb.',
  'Quartic slice CM31.mul/CM31.square also used r23_product_u32_bounded and are now proved (not in PCUF_FOR_P3 as FAILED: they were obligation comments).'],
 'failed_shapes':[
  {'attempt':'PCVB_L002/L003','shape':'closer used `rfl` for U64.max literal; `step*` closers with `omega` on nested mod 2^31/2^32','result':'rfl not accepted for U64.max; replaced with scalar_tac (h64d)'},
  {'attempt':'PCVB_L003-L006','shape':'single `omega` on the nested two-fold reduction value (recursion depth reached)','result':'replaced by factored lemmas mA/mB/core (PCVB_M31), each a small omega'},
  {'attempt':'PCVB_L008','shape':'core arithmetic under hypothesis x < 2^62','result':'FALSE (counterexample x = 2^62-1 = P^2+2P); replaced by the guard-derived bound x <= P^2'},
  {'attempt':'PCVB_L020','shape':'monolithic `simp only [defs, Nat.add_mul, Nat.mul_add]; omega` over the whole QM31 chain, exit 124 at 180 s (peak RSS 0.1 GiB, no memory pressure)','result':'RETIRED. Replaced by collapse lemmas sb_mod/mulsum + per-limb omega over product atoms (PCVB_L022: 1.6 s)'},
  {'attempt':'PCVB_L027-L034','shape':'r24_canonical_mul by `step*` with `simp at *` plus sixteen product-fact tries per goal; step* stopped at `lift (FromU64U32.from P)`; heartbeat 400000 reached (L034, 101 s)','result':'RETIRED. Replaced by liftfrom_spec, product facts established once up front, and the split r24_none / r24_canon (PCVB_L037)'}],
 'items':cl}
(E/'PCVB_CLASSIFICATION.json').write_text(json.dumps(classification,indent=1)+'\n')
rem=[x for x in cl if x['p3b_status']!='RESOLVED_P3B']
(E/'PCVB_REMAINING.json').write_text(json.dumps({'schema':'PCVB_REMAINING/1','target_established':False,'n_remaining':len(rem),'of':len(cl),
  'note':'Priority-2 items of PCUF_FOR_P3.json not proved in P3b. Heartbeat items are not raised. NO_FRESH_EMISSION (313), TEXT_ONLY (23), TEXT_IDENTICAL_ONLY (5), TEXT_DIFFERS (2), NO_COMMON_LEAN_NAME (1) items of PCUF_FOR_P3 are not in this list; they need extractions (see PCVB_NEED_EXTRACTION.json for the cone modules).',
  'items':rem},indent=1)+'\n')
# status of new theorems
st=[]
for a,fn,mod in [('PCVB_L040','PRVEq_AspisR72Sampler_Funs_P3.lean','AspisR72Sampler.Funs'),('PCVB_L041','PRVEq_AspisV8R19_QuarticFieldSlice_P3.lean','AspisV8R19.QuarticFieldSlice'),
                 ('PCVB_L042','PRVEq_AspisV8R19_ComplexFieldSlice_P3.lean','AspisV8R19.ComplexFieldSlice'),('PCVB_L043','PRVEq_AspisV8R19_GuardedFieldSlice_P3.lean','AspisV8R19.GuardedFieldSlice')]:
    r=json.load(open(E/a/'receipt.json'))
    ax=r['print_axioms']
    st.append({'module':mod,'file':fn,'sha256':hashlib.sha256((E/fn).read_bytes()).hexdigest(),'receipt':a+'/receipt.json','exit_status':r['exit_status'],'wall_seconds':r['wall_seconds'],'peak_rss_kib':int(r['peak_rss_kib']),'swaps':r['swaps'],
      'n_axiom_lines':len(ax),'all_standard_axioms_only':all(('sorryAx' not in x and 'native' not in x.lower()) for x in ax),'print_axioms':ax,'source_revision_at_launch':r['source_revision'],'source_tree_dirty_at_launch':r['source_tree_dirty']})
(E/'PCVB_STATUS.json').write_text(json.dumps({'schema':'PCVB_STATUS/1','target_established':False,'frozen':'4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',
 'claims':[
  {'id':'M31.mul','statement':'for each gate module, `@PRVFresh_<M>.field.M31.mul = @<gate ns>.field.M31.mul` (equality of functions M31 -> M31 -> Result M31, no hypotheses)','modules':['AspisR72Sampler.Funs','AspisV8R19.ComplexFieldSlice','AspisV8R19.GuardedFieldSlice','AspisV8R19.QuarticFieldSlice'],'proof':'case split on the two guards of the gate body; guarded branch by PCVB_M31.fast_chain (fastBody = redBody for products <= P^2), unguarded branches are syntactically the fresh chain'},
  {'id':'CM31.mul/CM31.square','statement':'fresh = gate as functions, R72Sampler and Quartic slice','proof':'M31.mul, M31.reduce_u64, M31.sub, M31.double equalities plus gate helper r23_product_u32_bounded = plain checked u64 product (theorem r23_gate)'},
  {'id':'QM31.mul','statement':'@PRVFresh_AspisR72Sampler_Funs.field.QM31.mul = @AspisR72Sampler.field.QM31.mul','proof':'r24_none (some limb >= P gives ok none), r24_canon (all limbs < P gives ok (some res) with res limbs = PCVB_QM.gateQ), chain_spec (gate Karatsuba chain limbs = PCVB_QM.qmul), PCVB_QM.comp0..comp3 (qmul = gateQ, omega over product atoms)'},
  {'id':'QM31.square','statement':'fresh = gate, R72Sampler','proof':'congruence on CM31.* equalities'}],
 'files':st,
 'what_is_not_claimed':['Equalities are against the P2f fresh emissions (PCQF_aspis_core_field_a sha256 3fe20d13..., PCQF_aspis_r1_cost_probe_candidate sha256 04b39d85... for the Guarded slice) as recorded by P2f; P3b re-extracted nothing.','No claim about any definition outside the four modules; the remaining 46 items are open (PCVB_REMAINING.json).','A theorem compiling is not evidence that the gate module is the one used by R1; PCXA_NONFROZEN.json lists AspisR72Sampler as extracted from a non-frozen source blob (a47a9996aa63); these theorems show its field functions equal the frozen ones, they do not make its other definitions frozen-equal.']},indent=1)+'\n')
(E/'PCVB_HAND_MODELS.json').write_text(json.dumps({'schema':'PCVB_HAND_MODELS/1','hand_models_standing_in_for_gate_or_fresh_definitions':[],
 'proof_internal_models':[
  {'name':'PCVB_QM.mm/sb/ad/clos/cmm/mulr/qmul/gateQ','kind':'Nat models of the limb arithmetic used inside proofs','connected_to':'M31/CM31 specs (m31mul_spec, cm31add_spec, cm31sub_spec, cm31mul_spec, mulr_spec) -> chain_spec; r24_canon; both are Aeneas-level theorems about the extracted constants','not_a_hand_model_because':'every use is through a theorem whose statement mentions the extracted gate constants'},
  {'name':'PCVB_M31.redBody/fastBody and PCVB_R23.r23','kind':'local copies of extracted bodies','connected_to':'gate constants by `rfl` (definitional unfolding checked by the compiler in fast_chain applications, red_spec_G and r23_gate)'}],
 'record_only':True,'trust_rows_proposed':[]},indent=1)+'\n')
(E/'PCVB_TOOLS.json').write_text(json.dumps({'schema':'PCVB_TOOLS/1','reused_from_P3a':{'PCVA_run.py':'-> PCVB_run.py (renamed PCVA->PCVB, host base codex-pc-prov-p3b-20261109, Stream C share check < 2 as the 2026-11-09 brief requires)','PCVA_run_host.py':'-> PCVB_run_host.py (renamed only)'},
 'new':{'PCVB_p3m31.py':'rewrites a P2f PRVEq equality file: inserts generic lemmas, replaces the M31.mul obligation by the all-inputs proof, turns dependent obligations into S2 theorems (callee list now includes theorems produced earlier in the same pass), --r23 adds the gate r23 theorem, --qm and --qm31-block insert the QM31.mul development','PCVB_m31_lemmas.lean / PCVB_r23_lemmas.lean / PCVB_qm_lemmas.lean / PCVB_R72_qm31_part1-5.lean':'sources of the inserted Lean','PCVB_nonfrozen.py':'builds PCVB_NONFROZEN_STATUS.json and PCVB_NEED_EXTRACTION.json','PCVB_deliver.py':'writes classification/status/remaining/hand-model/tools JSON'},
 'sha256':{k:hashlib.sha256((E/k).read_bytes()).hexdigest() for k in ['PCVB_run.py','PCVB_run_host.py','PCVB_p3m31.py','PCVB_nonfrozen.py','PCVB_m31_lemmas.lean','PCVB_r23_lemmas.lean','PCVB_qm_lemmas.lean','PCVB_R72_qm31_block.lean']},
 'lean_environment':'gate toolchain leanprover/lean4 v4.32.0 via lake env lean -j1 -M7000 -DElab.async=false; LEAN_PATH = PCVB_exports + ledger30 NNN_PATHS.json chain; Aeneas as in the gate path','scopes':'43 Lean scopes, 0 extraction, one at a time, 6G/8G, swap 0, 180 s; no scope killed by memory; one timeout (PCVB_L020, exit 124)'},indent=1)+'\n')
print(classification['counts_by_p3b_status'],classification['counts_by_class'])
