"""Same conservative lexical reachability method as ledger27; no new provenance claim."""
from pathlib import Path
import json,lzma,hashlib,subprocess
E=Path(__file__).resolve().parent;H=lambda b:hashlib.sha256(b).hexdigest()
def gitraw(p,rev='HEAD'):return subprocess.check_output(['git','show',rev+':'+p])
ns={};exec(compile(gitraw('evidence/emission-repro-20261110/NMH_names.py'),'NMH_names.py','exec'),ns)
p=json.loads(gitraw('evidence/emission-repro2-20261110/NML_PROVENANCE.json'));inv=json.loads(gitraw('evidence/emission-repro-20261110/NMH_INVENTORY.json'));blobs={b['blob']:b for b in inv['blobs']};prior=json.loads((E.parent/'ledger29-20261111/NNM_PROVENANCE.json').read_text())
roots={c['row']:c['theorem']for c in json.loads((E/'NNN_CANDIDATE_REVIEW.json').read_text())['candidates']};reach={};receipts={};hits={r:[]for r in roots}
for row,name in roots.items():
 paths=list((E.parent/'fin-host-20261108/NNO_raw').glob('*_'+name+'_REACHABLE.txt.xz'));assert len(paths)==1,(row,paths)
 raw=lzma.decompress(paths[0].read_bytes());assert H(raw)==Path(str(paths[0])[:-3]+'.sha256').read_text().strip();reach[row]=set(raw.decode().splitlines());receipts[row]=dict(root=name,path=str(paths[0]),sha256=H(raw))
for record in p['blobs']:
 if record['verdict']in['REPRODUCED','REPRODUCED_FROM_ARCHIVE']:continue
 b=blobs[record['blob']];names=ns['declarations'](gitraw(b['paths'][0],inv['revision']).decode())
 for row,rs in reach.items():
  matching={d['name']for d in names if d['name']in rs}
  for d in names:
   if d['private']:matching.update(n for n in rs if n.startswith('_private.')and n.endswith('.'+d['name']))
  if matching:hits[row].append(dict(blob=record['blob'],verdict=record['verdict'],names=sorted(matching)))
affected=set(prior['current_conservative_affected_CLOSED_rows'])|{row for row,hh in hits.items()if hh}
out=dict(prior);out.update(prior_closed_impact=len(prior['current_conservative_affected_CLOSED_rows']),current_conservative_affected_CLOSED_rows=sorted(affected),new_closed_impact_if_promoted=len(affected),new_rows_hits=hits,root_receipts=receipts,method=p['impact_method'],gate_reachability_used=True,input_pins={n:H(gitraw(n))for n in['evidence/emission-repro-20261110/NMH_names.py','evidence/emission-repro-20261110/NMH_INVENTORY.json','evidence/emission-repro2-20261110/NML_PROVENANCE.json']},no_row_reopened=True,bk='Historical line unchanged. Fresh NMW parent emissions and source fission do not reproduce every inherited child blob; release re-extraction/per-definition equalities remain open.')
out['rulings']=list(dict.fromkeys(prior.get('rulings',[])+['bt','TGA_ merged audit','TGB_ merged audit']))
out['PRV_plan']=dict(source='evidence/prov-plan-20261108/PRV_REPORT.md',source_sha256=H(gitraw('evidence/prov-plan-20261108/PRV_REPORT.md')),accurate_affected_range=[532,538],basis_closed_rows=587,note='PRV source-linked assessment retained separately from historical same-method conservative lexical count; no row reopened or trust row changed')
(E/'NNN_PROVENANCE.json').write_text(json.dumps(out,indent=1)+'\n');print(json.dumps(dict(affected=len(affected),new_row_blob_counts={r:len(h)for r,h in hits.items()})))
