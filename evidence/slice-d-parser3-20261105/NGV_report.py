"""Materialize only reviewed NGV additive rows after their combined/raw gates."""
from pathlib import Path
import json,lzma,hashlib,re,sys
E=Path(__file__).resolve().parent;R=E.parents[1]
J=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
write=lambda n,x:(E/n).write_text(json.dumps(x,indent=2)+'\n')
selected=sys.argv[1].split(',');attempt=sys.argv[2];combined=sys.argv[3]
base=R/'evidence/inv-repair-20261104/NGB_ADMITTED_LEDGER.json.xz';old={r['row']:r for r in json.loads(lzma.decompress(base.read_bytes()))['rows']}
roots={'TX1:151':('NGV_ParsePacket.result','NGV_ParsePacket',[[45,46],[47,48],[49,50]],'Every original framed record of length <=3717; all row bytes. Validator domain <=3712 derived from the selected original payload; full rejected prefixes.'),
'TX1:152':('NGV_AtPacket.result','NGV_AtPacket',[[55,56],[57,58]],'Every original row <27 at its source cursor dst(row), arbitrary bytes. Both additions derived independently of parsing; get None/errors retained.'),
'TX1:098':('NGV_SemanticPacket.result','NGV_SemanticPacket',[[59,60],[61,62],[92,93],[94,95]],'Same original 7015-byte compact input and arbitrary 13831-byte output; full row schedule and same-window frames.')}
assert selected and set(selected)<=set(roots)
summary=attempt+'_audit/SUMMARY.json';scan=attempt+'_audit/LOADED_scan.jsonl';assert J(E/summary)['status']=='PASS'
write('NGV_AUDIT.json',dict(summary=summary,scan=scan,attempts=[combined,attempt],kind='Focused cached-cohort combined replay, raw ax2 and NFX loaded scan; not cold release replay'))
imports=re.findall(r'^import (NGV_\S+)',(E/'NGV_COMBINED_IMPORT.lean').read_text(),re.M)
sourcepins=[dict(path=m+'.lean',sha256=sha(E/(m+'.lean')))for m in imports]
functions=[];edges=[];changes=[]
prior=J(R/'evidence/slice-d-parser-20261104/NGD_EDGES.json')
for row in selected:
 r=old[row];root,module,pairs,domain=roots[row]
 functions.append(dict(function=r['function'],rows=[row],status='CLOSED',form='Hybrid (y), original native local-record/KMX certificates plus emitted/model packet induction',frozen_body_sha256=r['frozen_body_sha256'],lean_root=root,canonical_module=module,domain=domain,native_pairs=[[f'NGD_K{n:03}'for n in pair]for pair in pairs],sources=sourcepins,inner_hypotheses_remaining=[],retained_root_interpretation='P6/D188 option A semantic transport; compiler/Aeneas/library/SDK/ABI/std/allocator/source-to-ELF realization and accepted runtime and cryptographic rows retained',domain_roots=['NGV_Validator.result','NGV_ParsePacket.result']+(['NGV_DecodeAfterParse.result']if row=='TX1:151'else ['NGV_AtPacket.result']if row=='TX1:152'else [])))
 for callee in r['canonical_callees']:
  p=next(e for e in prior if e['row']==row and e['callee']==callee)
  proof='NFQ_RowShape.prefix_reference'if callee.endswith('::row_shape')else 'NGV_Validator.result'if callee.endswith('::validate_record_fields')else 'NGV_AtPacket.result'if callee.endswith('::parse_record')else root
  edges.append(dict(row=row,caller=r['function'],callee=callee,status='CLOSED',proof=proof,citation=p.get('callee_citation')or dict(path='NGV_CLOSED.json',root='NGV_ParsePacket.result'),domain=domain))
 changes.append(dict(row=row,function=r['function'],before='OPEN',after='CLOSED',frozen_body_sha256=r['frozen_body_sha256'],certificate='NGV_CLOSED.json',lean_root=root))
write('NGV_CLOSED.json',dict(schema_version=1,frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',new_composed_functions=len(functions),new_composed_rows=len(functions),driver_root_status='OPEN',functions=functions,other_members=[dict(row=row,status='OPEN')for row in roots if row not in selected],trust_rows_removed=[],trust_rows_added=[]))
write('NGV_EDGES.json',edges)
write('NGV_LEDGER_DELTA.json',dict(schema_version=1,checks_added_only=True,baseline=str(base.relative_to(R)),baseline_sha256=sha(base),new_closed_rows=selected,rows=changes,no_other_status_change=True,not_a_global_refresh=True))
