"""Pure report projection from the final checked artifact; no proof replay."""
import json,re
from pathlib import Path
import NEX_validate as v
E=v.E;p=v.read(E/'NEX_LEDGER_DELTA.json');audit=v.read(E/'NEX_STOP_AUDIT.json')
edge=v.read(E/'NEX_EDGES.json')
for e in edge['edges']:
 c=p.get('edges',{}).get(e['edge'])
 if c:
  e['certificate']={'overlay':'NEX_LEDGER_DELTA.json.xz','group':'edges','subject':e['edge'],'semantic_review_sha256':c['semantic_review_sha256'],'theorems':[t['name'] for t in c.get('domain_theorems',[])],'native_receipts':[r for r in c.get('support',[]) if r['path'].endswith('/receipt.json')]}
  if c['id'].startswith('NEX_'):
   e['previous_classification']=e.get('previous_classification',e['classification']);e['classification']='native full-Result call-domain/frame and symbolic model substitution; safe Box ruling(aa) where recorded'
 if e['status']=='CLOSED':e['exact_obstacle']=None
(E/'NEX_EDGES.json').write_text(json.dumps(edge,indent=1)+'\n')
f=E/'NEX_COMPOSED.md';text=f.read_text()
for x in audit['root_results']:
 if x['status']!='OPEN':continue
 heading='## '+x['function']+'\n';start=text.index(heading);end=text.find('\n## ',start+len(heading));end=len(text) if end<0 else end
 text=text[:start]+heading+'\nStatus: OPEN. No composed native theorem established.\n\n'+x['exact_remaining_obligation']+'\n\nRequired explicit native bridge hypotheses remain unresolved; no root bridge is assumed to certify itself.\n'+text[end:]
text=text.split('\n## Root hypothesis and trust inventory',1)[0]
text+='''
## Root hypothesis and trust inventory

The two CLOSED hybrid certificates retain CompositionTrustOptionA explicitly and have no remaining inner named hypotheses. Their model statements quantify all typed Statements and unchanged state, with the stated exact ordered trace. Native physical/ABI/packet interpretations and the unchanged approved NDT trust rows, including RuntimePersistence, remain in the release argument. No added runtime trust is used by either CLOSED root. The five OPEN roots have no accepted complete native theorem; explicit missing child/caller bridges above cannot be replaced by root-owned PacketDomain or PhysicalInterpretation.

Final checked edges:93 CLOSED,36 OPEN, all129 retained. Budget140/140 Kani,40/60 Lean. NEX_L040 audits52 theorem references from27 accepted modules with only standard axioms. Final per-member stop reasons and every remaining native witness are in NEX_STOP_AUDIT.json. Target not yet established.
'''
f.write_text(text)
