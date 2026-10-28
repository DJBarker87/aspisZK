from pathlib import Path
import json,subprocess,hashlib,re
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-dlib-20261028';before=json.loads((E/'rows-before.json').read_text())
proofs={
'V187':[],
'V201':['EncoderControl.source_reference','EncoderSelected.consumed','EncoderPairs.coordinate','EncoderBasis.native_min'],
'V231':['FinalizeParam.source','FinalizeParam.callback_count','CompressionTrace.backend_instances'],
'V234':['Forwarding.output','Forwarding.failure'],
'V235':['Forwarding.output','Forwarding.failure'],
'V236':['UpdateEvents.append','UpdateEvents.complete','UpdateEvents.pending'],
'V237':['DefaultNative.native_callback','DefaultNative.consumed','WrapLaw.source_reference'],
'V238':['Forwarding.ct_restoration','Forwarding.ct_length','Truncation.length','Truncation.full']}
native={
'V187':'Exact shipped generic entry Charon accepted; pinned Aeneas rejected structured Drop. Empty non-Copy Drop Vec N0/N1 Kani PASS only, no populated element-copy claim.',
'V201':'Four complete native source bodies token-pinned; 128 dense M31/QM31 finite differential cases and changed-write/sparse witnesses PASS. Universal native iterator/source association remains open.',
'V231':'131072 native wrapper/padding coordinate fixtures PASS (finite validation only); Kani padding-05 PASS suspended under ruling r. Compression is an arbitrary Result-valued block parameter in Lean.',
'V234':'131072 combined native wrapper coordinate fixtures PASS, finite validation of forwarding only; generic Drop and complete source binding open.',
'V235':'131072 combined native wrapper coordinate fixtures PASS, finite validation of forwarding only; generic Drop and complete source binding open.',
'V236':'Two optimized Kani runs timed out at900s (whole trace and coordinate split), no proof/counterexample. No third same-bound run; no generic native update association.',
'V237':'Kani constructor PASS1/2 conservatively suspended under ruling r; Lean selected64/model constructors remain checked. No accepted native-link closure.',
'V238':'131072 combined native fixtures PASS including left/right28 and full32 truncation, mutated core and reset buffer; finite validation only.'}
nstatus={
'V187':'No credited generic emission. Exact native extraction rejected; no escaping/write-back credit inferred.',
'V201':'Owned emission inspected: basis_cell returns Array.update; fill/round bind updated arrays. Native changed-write comparison passed. Corrected EncoderMutation kernel witness was refused at42296 and remains uncompiled.',
'V231':'CBL padding emission explicitly threads every changed array and retains first buffer in two-block branch; full owned content law privately compiled. Native finite retained-buffer comparison passed. Original borrowed source association open.',
'V234':'Native finite callback mutates output/core/buffer and forwarding checks output. No rejected shipped emission credited; generic Drop open.',
'V235':'Native finite callback mutates output/core/buffer and forwarding checks output. No rejected shipped emission credited; generic Drop open.',
'V236':'No accepted shipped/reference extraction; native update gates timed out; no mutable-borrow fidelity claim.',
'V237':'Owned constructors have no mutable borrowed iterator writes. Rejected generic wrapper emission is not credited. Native Kani credit suspended separately under r.',
'V238':'Native finite callback changes inner core and resets buffer; both observed after Ct wrapper. Lean Ct model retains both returned values. Native generic copy/source association open.'}
rows=[]
for b in before:
 rid=b['id'];d=E/rid;d.mkdir(exist_ok=True)
 j=dict(row=rid,name=b['name'],status='OPEN; supporting model/reference theorems only; no accepted native closure',before_residual=b['residual_fields'],after_residual=b['residual_fields'],residual_removed=False,closing_theorem=None,supporting_theorems=['R1Z.PV_DL_'+x for x in proofs[rid]],native_evidence_class=native[rid],ruling_n=nstatus[rid],nonvacuity=('empty native Vec control witnesses; arbitrary ownership spec uncompiled' if rid=='V187' else 'EncoderControl.inputs_nonempty plus native finite successful witnesses' if rid=='V201' else 'DefaultBuffer.nonvacuous and DefaultLaw.nonvacuous' if rid=='V237' else 'Audit.padding_domain and finite native successful fixtures' if rid=='V231' else 'finite successful/mutating native callbacks; generic model preserves original Result inputs'),deployed_premises_removed=0,trust_fields_added=0,retained='Native/source/caller/compiler association; real RunJoin and L1/L2/L3 remain. V232 unchanged.',receipt_index='../receipts-index.json')
 (d/'status.json').write_text(json.dumps(j,indent=2)+'\n');rows.append(j)
(E/'rows-after.json').write_text(json.dumps(rows,indent=2)+'\n')
receipts=[]
for p in sorted(E.glob('*/receipt.json')):
 j=json.loads(p.read_text());receipts.append(dict(path=str(p.relative_to(E)),**{k:j.get(k) for k in ['target','module','attempt','exit','wall','peak_rss_kib','swap','source_revision','revision','print_axioms','bound','native_link_class','credit_status']}))
(E/'receipts-index.json').write_text(json.dumps(receipts,indent=2)+'\n')
(E/'commits.log').write_text(subprocess.check_output(['git','log','--oneline','b3ad0edf5b..HEAD'],text=True))
passed={j.get('module'):j for j in receipts if j['exit']==0 and j.get('module')}
drafts=[]
for p in sorted((R/'docs/research/v8-r0-zk-20261009/lean/R1Z').glob('PV_DL_*.lean')):
 m='R1Z/'+p.stem;j=passed.get(m)
 if j is None:drafts.append(m)
(E/'uncompiled-drafts.json').write_text(json.dumps(drafts,indent=2)+'\n')
print(len(rows),'rows OPEN;',len(receipts),'receipts;',len(drafts),'uncompiled drafts')
