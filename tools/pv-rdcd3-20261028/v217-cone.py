"""Disposition all conservative matches by concrete receiver and Result scope.
Counts alone do not prove a cone complete or restore a row.
"""
from pathlib import Path
import json,lzma,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rdcd3-20261028'
p=R/'evidence/pv-rdcd-20261028/typed-reached-static.json.xz'
j=next(x for x in json.loads(lzma.open(p).read()) if x['id']=='V217');records=[]
for x in j['unresolved']:
 f,c=x['function'],x['call']
 if f.startswith('alloc::'):
  kind='excluded concrete receiver'
  reason='The complete application bodies contain ops::Range<usize>, fixed arrays and Copy field records. No BTreeMap/BTreeSet, tree node, KV storage or alloc::Range is constructed or passed. The generic printed-name match is not this concrete receiver.'
  law='v217-application-source-result.json; range-source-result.json dispatch checks'
 elif '::spec_next' in c or 'Range<usize> as Iterator>::next' in c:
  kind='concrete range source law'
  reason='ops::Range<usize> uses TrustedStep; next updates start and returns the previous value, preserving complete range state. Fixed ranges have explicit reachable-index rank proofs.'
  law='CB_ForwardRange.next_done/next_step; CB_ForwardLoop.source; CB_MaskFillBody.c1/mask; CB_FillLoopsEq.c1/mask'
 elif 'panic_impl' in c:
  kind='terminal Result projection'
  reason='Index failure and invalid tower coordinate are terminal at the Result interface; all reached fixed indices are proved safe. The invalid-coordinate helper still retains its failure arm. Panic text, runtime effects and physical observer behavior are separate retained obligations.'
  law='Index194.failure; ArrayWrite194.complete; CB_MaskLeaves.tower; CB_MaskIndices.coordinate'
 elif 'str>::len' in c:
  kind='panic diagnostic outside value projection'
  reason='This record constructs panic diagnostics, not a successful field result or loop state. No diagnostic/world/observer law is inferred from Result equality; those obligations remain explicitly retained.'
  law='Control194.panic_terminal; source/Result scope qualification'
 else:raise AssertionError(x)
 records.append(dict(**x,disposition=kind,argument=reason,law=law))
assert len(records)==20
out=dict(row='V217',input_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),records=records,additional_reached_bodies='Six complete reverse bodies, six complete mask application bodies and 26 field bodies are recorded separately, as well as range/index/write/widening/wrapping primitives. This conservative inventory is not treated as exhaustive merely because all20 are classified.',scope='Complete source-value/Result only after matching successful root/closing proof receipts and coherent DAG; compiler V370/D381/D386, native RunJoin/world/observer and physical effects retained.',composition='Reclassification within existing Aeneas/Rust semantics; no endpoint premise removal')
(E/'v217-cone-disposition.json').write_text(json.dumps(out,indent=2)+'\n')
