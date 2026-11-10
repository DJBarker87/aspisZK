#!/usr/bin/env python3
"""Writes PCWQ_MAP.json, PCWQ_STATUS.json, PCWQ_REMAINING.json, PCWQ_CLASSIFICATIONS.json, PCWQ_TOOLS.json, PCWQ_PINS.json."""
import json,hashlib,sys,re
sys.dont_write_bytecode=True
sha=lambda p:hashlib.sha256(open(p,'rb').read()).hexdigest()
REV='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
Q1='PRVEq_RPz7_WAdm_Fissioned_Funs_q1.lean'; Q2='PRVEq_RPz7_WAdm_Fissioned_Types_q2.lean'
P='WAdm_Fissioned.PRVQ.'
F='crates/aspis-r1-cost-probe/src/verifier.rs'
G='evidence/writer-adm-20261025/WAdm_NativeFixture/WAdm_model.rs'
HM_D='HM-D (array: core::array::iter::{IntoIterator for [T;N]}::into_iter and {Iterator for IntoIter}::next; the gate gives them concrete list definitions, the fresh emission leaves them external)'
HM_B='HM-B (core slice iterator: core::slice::iter::{Iterator for Iter}::next and <&[T;N] as IntoIterator>::into_iter, both defined in the Aeneas library as slice+index)'
VECREF='alloc::vec::{impl IntoIterator for &Vec<T>}::into_iter (external in the fresh emission, no model in the Aeneas library; carried as the parameter SVI with premise hS; nearest row HM-B, row assignment is the lead decision)'
TOLE='aspis_core::field::wide_exact::WideExact::to_le_bytes (Aspis function, left external by the fresh emission; the gate gives it the hand model AspisR1.CheckpointBytesE.rawBytes; bound by name, CONDITIONAL_ON_BINDING)'
defs=[]
def add(key,gate_lines,frozen,frozen_lines,cls,theorems,deps,note=''):
    defs.append(dict(key='WAdm_Fissioned.WAdm_model.'+key,gate_source=G+':'+gate_lines,frozen_counterpart=frozen,frozen_lines=frozen_lines,**{'class':cls},theorems=[P+t for t in theorems],depends_on=deps,note=note))
add('WAdm_putK','28:0-30:1','verifier::put_k',F+':325','EQUALITY_PROVED',['E_putK','E_putK_fun','E_wlb'],[],
    'fresh put_k (with the fresh QM31::write_le_bytes and M31::to_le_bytes bodies, aspis-core field.rs 1028 and 248) equals the gate constant by rfl; leaf types TYPE_ISOMORPHISM in q2')
for g,fz,gl,fl,loopthm,bodythm,hm,extra in [
 ('early','checkpoint_loop1','20:0-22:1 (loop 21:4-21:60)','331:4-331:71',['E_loop1','E_loop1_fun','K_early'],'E_body1',HM_D,[TOLE]),
 ('tail','checkpoint_loop5','24:0-26:1 (loop 25:4-25:60)','336:4-336:47',['E_loop5','E_loop5_fun','K_tail'],'E_body5',HM_D,[TOLE]),
 ('queries','checkpoint_loop2','32:0-34:1 (loop 33:4-33:60)','333:4-333:65',['E_loop2','E_loop2_fun','K_queries'],'E_body2',HM_D,[]),
 ('semantic','checkpoint_loop3','36:0-38:1 (loop 37:4-37:44)','334:4-334:100',['E_loop3','E_loop3_fun','K_semantic'],'E_body3',HM_D,[]),
]:
    add('WAdm_%s_loop.body'%g,gl.split(' ')[0] if False else gl.split('(loop ')[1].rstrip(')'),'verifier::%s.body'%fz,F+':'+fl,'DEPENDS_ON_LIBRARY_TRUST',[bodythm],[hm]+extra,'body-level function equality fresh = gate (same iterator-next constant on both sides)')
    add('WAdm_%s_loop'%g,gl.split('(loop ')[1].rstrip(')'),'verifier::%s'%fz,F+':'+fl,'DEPENDS_ON_LIBRARY_TRUST',loopthm[:2],[hm]+extra,'function equality fresh loop = gate loop')
    add('WAdm_%s'%g,gl.split(' ')[0],'(none: the frozen source writes the segment inline in checkpoint as `into_iter` of an array literal then the loop)',F+':326-341','GATE_ONLY_HELPER',[loopthm[2]],[hm]+extra,'model helper; cleared through the continuation-form equality of the frozen iterator-plus-loop prefix')
add('WAdm_roots_loop.body','17:4-17:55','verifier::checkpoint_loop0.body (iterates `&p.roots`, a slice::Iter; the gate iterates the array by value)',F+':330:4-330:55','DEPENDS_ON_LIBRARY_TRUST',['F_loop0','G_roots'],[HM_B,HM_D],'different iterator representation: related by closed form fold over the remaining list')
add('WAdm_roots_loop','17:4-17:55','verifier::checkpoint_loop0',F+':330:4-330:55','DEPENDS_ON_LIBRARY_TRUST',['E_loop0'],[HM_B,HM_D],'checkpoint_loop0 it out = WAdm_roots_loop (it.slice.val.drop it.i) out')
add('WAdm_roots','16:0-18:1','(none: inline `for root in &p.roots`)',F+':326-341','GATE_ONLY_HELPER',['K_roots'],[HM_B,HM_D])
add('WAdm_coordinates_loop.body','41:4-41:44','verifier::checkpoint_loop4.body / checkpoint_loop4_loop0.body (nested loops over SecureCirclePoint then [x,y]; the gate has one flat loop over four QM31)',F+':335:4-335:108','DEPENDS_ON_LIBRARY_TRUST',['F_loop4','F_loop4_0','G_coord','coord_fold'],[HM_D])
add('WAdm_coordinates_loop','41:4-41:44','verifier::checkpoint_loop4',F+':335:4-335:108','DEPENDS_ON_LIBRARY_TRUST',['E_loop4'],[HM_D],'checkpoint_loop4 pts out = WAdm_coordinates_loop (pts.flatMap (fun z => [z.x, z.y])) out')
add('WAdm_coordinates','40:0-42:1','(none: inline nested loop)',F+':335',  'GATE_ONLY_HELPER',['K_coord','arr2'],[HM_D])
add('WAdm_weights_loop.body','45:4-45:44','verifier::checkpoint_loop6.body (iterates `&a.weights`, slice::Iter; the gate iterates the Vec by value)',F+':338:4-338:45','DEPENDS_ON_LIBRARY_TRUST',['F_loop6','G_weights'],[HM_B,VECREF])
add('WAdm_weights_loop','45:4-45:44','verifier::checkpoint_loop6',F+':338:4-338:45','DEPENDS_ON_LIBRARY_TRUST',['E_loop6'],[HM_B,VECREF],'premise v.val = it.slice.val.drop it.i')
add('WAdm_weights','44:0-46:1','(none: inline `for &x in &a.weights`)',F+':338','GATE_ONLY_HELPER',['K_weights'],[HM_B,VECREF],'premise hS on the parameter SVI')
add('WAdm_fields','10:0-14:1','(none: the frozen checkpoint reads the Prepared and Accumulator fields directly)',F+':326-341','GATE_ONLY_HELPER',['checkpoint_eq','arr2'],[],'record builder; unfolded inside checkpoint_eq')
add('WAdm_checkpoint','50:0-62:1','verifier::checkpoint',F+':326-341','DEPENDS_ON_LIBRARY_TRUST',['checkpoint_eq','cs_S2'],[HM_D,HM_B,VECREF,TOLE],
    'restricted domain: variant = S2, a.next = 10, weights length 64 (the gate hard-codes them); not an all-input equality')
assert len(defs)==24,len(defs)
keys=[d['key'] for d in defs]
tri=json.load(open('../prov-p5a-20261110/PCWJ_TRIAGE.json'))
want=sorted(r['definition'] for r in tri['records'] if r['module']=='RPz7_WAdm_Fissioned_Funs')
assert sorted(keys)==want,(set(keys)^set(want))
from collections import Counter
cnt=Counter(d['class'] for d in defs)
MAP=dict(schema='PCWQ_MAP/1',target_established=False,frozen_revision=REV,pool_revision='b936275465600469312d1f058cdc91ea2a11f3dc',
 op16=dict(installed_by='WAdm_NativeInstall.on_run installs the native op16 (writer_slot, other_slots) (evidence/writer-adm-20261025/HANDOFF.md); the model WAdm_model.rs was checked by Kani against the unchanged shipped verifier::checkpoint (WAdm_KANI001)',
  frozen_function='aspis_r1_cost_probe::verifier::checkpoint',file=F,lines='326-341',helpers={'put':F+':324','put_k':F+':325','checkpoint_size':F+':32','CHECKPOINT_FIXED':F+':18','Variant::tag/folds/final_len':'crates/aspis-r1-cost-probe/src/transport.rs:6,8,9','QM31::write_le_bytes':'crates/aspis-core/src/field.rs:1028','M31::to_le_bytes':'crates/aspis-core/src/field.rs:248','WideExact::to_le_bytes':'crates/aspis-core/src/field/wide_exact.rs:273'},
  call_chain='programs/r1-cost-probe/src/lib.rs:42 first -> :49-50 first_decoded -> verifier::tx1 -> crates/aspis-r1-cost-probe/src/verifier/candidate.rs:288 `checkpoint(&p,&a,proof,public_bytes,hash)` (candidate.rs is mounted at verifier.rs:515)',
  other_callers='crates/aspis-r1-cost-probe/src/eight_way.rs:113 (feature audit-eight-way, audit only, not the release entrypoint)',
  pool_b936275='checked: programs/aspis-pool has no counterpart (only pair_cu_checkpoint CU markers and tests); op16 lives in crates/aspis-r1-cost-probe at 4bb3b3f'),
 definitions=defs)
json.dump(MAP,open('PCWQ_MAP.json','w'),indent=1)
STATUS=dict(schema='PCWQ_STATUS/1',target_established=False,frozen_revision=REV,branch='codex/pc-prov-p5g-20261110',
 summary='RPz7_WAdm_Fissioned_Funs 24 of 24 definitions carry a kernel-checked relation to the frozen op16 writer path (verifier::checkpoint); none is OPEN. EQUALITY_PROVED 1, GATE_ONLY_HELPER 8, DEPENDS_ON_LIBRARY_TRUST 15 (the loop and body definitions and checkpoint itself, naming HM-D, HM-B and the unmodelled &Vec into_iter). No definition is credited as unconditional beyond putK.',
 counts=dict(cnt),
 files={Q1:sha(Q1),Q2:sha(Q2)},
 lean_scopes='12 of 20 (PCWQ_L001-L012); exit 0: L009 (superseded), L011 (final q1), L012 (q2); exit 1 are failed shapes, see PCWQ_ATTEMPTS.jsonl and PCWQ_CLASSIFICATIONS.json',
 extraction_scopes='3 of 8 (PCWQ_E001-E003), all exit 0; E003 is the emission used',
 final_receipts=dict(q1='PCWQ_L011/receipt.json',q2='PCWQ_L012/receipt.json'),
 axioms='every theorem and Equiv: subsets of [propext, Classical.choice, Quot.sound] (receipts print_axioms); no unfinished-proof placeholder, no axiom, no native_decide, no raised maxHeartbeats (200000)',
 type_isomorphism=[dict(type=t,theorem='WAdm_Fissioned.PRVQT.'+n,file=Q2,class_='TYPE_ISOMORPHISM') for t,n in [('M31','m31Equiv'),('CM31','cm31Equiv'),('QM31','qm31Equiv'),('SecureCirclePoint','circlePointEquiv'),('WideExact','wideExactEquiv'),('Digest32','digest32Equiv')]]+
   [dict(type=t,theorem=P+n,file=Q1,class_='TYPE_ISOMORPHISM',note='fresh Variant, Prepared, Accumulator (frozen 4bb3b3f) against the gate/OraclePortCkptAbi2Extracted types, with the leaf types shared by name (the leaf isomorphisms are in q2)') for t,n in [('Variant','variantEquiv'),('Prepared','preparedEquiv'),('Accumulator','accumulatorEquiv')]],
 definitions=[{k:d[k] for k in ('key','class','theorems','depends_on','frozen_counterpart')} for d in defs],
 main_theorem=dict(name=P+'checkpoint_eq',statement='for all S (the external <&Vec<T> as IntoIterator>::into_iter as a parameter) with premise hS (S Global w = ok the slice iterator over w from index 0), all inst p a proof public hash with p.variant = S2, a.next = 10, length a.weights = 64: fresh verifier.checkpoint S inst p a proof public hash = (WAdm_fields (toGatePrepared p) a.rhs a.power >>= fun f => WAdm_checkpoint inst f a.weights proof public hash)',
  premises_kept=['hS (non-vacuous: hS_satisfiable)','p.variant = S2','a.next = 10#usize','alloc.vec.Vec.len a.weights = 64#usize'],
  not_claimed='all-input equality (the gate hard-codes S2, 10 and 64 weights); equality for other variants; the WideExact::to_le_bytes body; array and slice iterator library models'))
json.dump(STATUS,open('PCWQ_STATUS.json','w'),indent=1)
REM=dict(schema='PCWQ_REMAINING/1',target_established=False,items=[
 dict(id='R1',what='WideExact::to_le_bytes: fresh emission (PCWQ_E002) is a loop over to_limbs/chunks_exact_mut externals; the gate uses the hand model AspisR1.CheckpointBytesE.rawBytes. Early/tail loops, put and WAdm_checkpoint stay conditional on that binding until a fresh body is proved equal to rawBytes (needs models for core::slice::chunks_exact_mut and WideExact::to_limbs, library externals).',blocks=['early','tail','checkpoint']),
 dict(id='R2',what='array IntoIter (HM-D) and slice Iter (HM-B) models: the loop equalities hold with the gate list model for array IntoIter and the Aeneas library model for slice Iter; the fresh extraction leaves the array functions external, so they are bound by name. Row coverage is the lead decision.',blocks=['all loops, bodies and checkpoint']),
 dict(id='R3',what='<&Vec<T> as IntoIterator>::into_iter has no model in the Aeneas library: carried as parameter SVI with premise hS (non-vacuous). The lead assigns it to HM-B or another row, or a proof of an Aeneas library definition is added.',blocks=['weights','checkpoint']),
 dict(id='R4',what='domain: the gate WAdm_checkpoint hard-codes variant S2, next 10 and 64 weights, so the equality holds only there; frozen checkpoint is general. Whether the release argument needs more than the S2 / next 10 domain is a security-contract question, not decided here.',blocks=['checkpoint']),
 dict(id='R5',what='fresh Types of Prepared/Accumulator use the leaf types by name; the composed isomorphism with the fresh leaf types (Array of fresh WideExact etc.) is not formalised (nested Equiv, same class as PCWJ TYPES_NESTED_EQUIV_NOT_GENERATED); the leaf isomorphisms (q2) and the record isomorphisms over shared leaves (q1) are proved.',blocks=['types'])])
json.dump(REM,open('PCWQ_REMAINING.json','w'),indent=1)
TOOLS=dict(schema='PCWQ_TOOLS/1',copied={'PCWQ_run.py,PCWQ_run_host.py,PCWQ_extract.py,PCWQ_aeneas.py,PCWQ_mkspec.py,run_ext.sh,run_scope.sh,PCWQ_STAGER_PIN.json':'evidence/prov-p5a-20261110 PCWJ_ (renamed; host base codex-pc-prov-p5g-20261110; no other change); this is the latest generator lineage (prov-p3x PCWF_ -> p5a PCWJ_)'},
 new={'PCWQ_assemble.py':'assembles PRVEq_RPz7_WAdm_Fissioned_Funs_q1.lean from the fresh PCWQ_E003 emission (attributes rust_fun/rust_loop/rust_loop_body/rust_type removed, header options replaced, namespace PRVFresh_WAdm_q1; the only edit of emitted text is the name of the external <&Vec as IntoIterator>::into_iter inside checkpoint, replaced by the section variable SVI) and gen/q1_proofs_{a..e}.lean.in',
  'PCWQ_assemble_types.py':'assembles PRVEq_RPz7_WAdm_Fissioned_Types_q2.lean (fresh leaf types verbatim, Equiv proofs)','PCWQ_meta.py':'this file: MAP/STATUS/REMAINING/TOOLS/PINS/CLASSIFICATIONS'},
 sha256={f:sha(f) for f in ['PCWQ_run.py','PCWQ_run_host.py','PCWQ_extract.py','PCWQ_mkspec.py','PCWQ_assemble.py','PCWQ_assemble_types.py']},
 generic_lemmas='gen/q1_proofs_a.lean.in (loop_fold_gen: a loop whose body consumes a list view equals a monadic fold; slice-iterator step lemmas) copied in the file; PRVC_LoopBridge.lean was used only for bs/loop_unfold (copied)')
json.dump(TOOLS,open('PCWQ_TOOLS.json','w'),indent=1)
PINS=dict(schema='PCWQ_PINS/1',frozen_revision=REV,frozen_source_tree_git_hash='d461fbc56cec8ba29678d6613fc38e6c795d6a66',pool_revision='b936275465600469312d1f058cdc91ea2a11f3dc',
 extraction=dict(note='cargo --jobs 4, CARGO_BUILD_JOBS=4, rustc -Zthreads=1; identity by class receipt PCWE_E003; stable --dest-file with run_emitted/repro.llbc symlinked; original Aeneas 959659a6 (sha256 checked by PCWQ_extract.py); Charon XRa_bin; 180 s timeout never raised',
  runs={r:'%s_emitted/%s_PINS.json'%(r,r) for r in ['PCWQ_E001','PCWQ_E002','PCWQ_E003']},
  configuration='ON (CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS=true, -C overflow-checks=yes): the gate module has no NOX_R22_CONFIG record (UNDETERMINED); the gate body has no arithmetic beyond length checks, the frozen checkpoint_size arithmetic is checked (ON) and evaluated in cs_S2',
  roots={'E001':'crate::verifier::checkpoint (+WideExact included)','E002':'+ includes of field write_le_bytes and WideExact::to_le_bytes (shows the to_limbs/chunks_exact_mut externals)','E003':'+ includes of field write_le_bytes and field to_le_bytes (M31): the emission used'}),
 lean=dict(toolchain='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0',command='lake env lean -j1 -M7000 -DElab.async=false',objects='L187 replay closure /home/dombarker/project-offloads/codex-cx-replay-l187-20261109/objs by reference, then evidence/ledger30-20261111/NNN_PATHS.json chain',scope='MemoryHigh=6G MemoryMax=8G MemorySwapMax=0 TasksMax=64, timeout 180 s',
  source_files={Q1:sha(Q1),Q2:sha(Q2)}))
json.dump(PINS,open('PCWQ_PINS.json','w'),indent=1)
print(dict(cnt))
