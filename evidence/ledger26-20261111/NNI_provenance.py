from pathlib import Path
import json,lzma,hashlib,subprocess
E=Path(__file__).resolve().parent;H=lambda b:hashlib.sha256(b).hexdigest()
def gitraw(p,rev='HEAD'):return subprocess.check_output(['git','show',rev+':'+p])
ns={};exec(compile(gitraw('evidence/emission-repro-20261110/NMH_names.py'),'NMH_names.py','exec'),ns)
p=json.loads(gitraw('evidence/emission-repro2-20261110/NML_PROVENANCE.json'));inv=json.loads(gitraw('evidence/emission-repro-20261110/NMH_INVENTORY.json'));blobs={b['blob']:b for b in inv['blobs']};prior=json.loads((E.parent/'ledger25-20261111/NMQ_PROVENANCE.json').read_text());name='AspisR1.NNG_Candidate136.candidate'
paths=list(E.glob('NNI_NEP_*_'+name+'_REACHABLE.txt.xz'));source=paths[0]if paths else E.parent/('tx1-principal-20261111/NNG_C136_audit/proof0/NEP_proof0_'+name+'_REACHABLE.txt.xz');raw=lzma.decompress(source.read_bytes());assert H(raw)==Path(str(source)[:-3]+'.sha256').read_text().strip();reach=set(raw.decode().splitlines());hits=[]
for row in p['blobs']:
 if row['verdict']in['REPRODUCED','REPRODUCED_FROM_ARCHIVE']:continue
 b=blobs[row['blob']];text=gitraw(b['paths'][0],inv['revision']).decode();names=ns['declarations'](text);matching={d['name']for d in names if d['name']in reach}
 for d in names:
  if d['private']:matching.update(n for n in reach if n.startswith('_private.')and n.endswith('.'+d['name']))
 if matching:hits.append(dict(blob=row['blob'],verdict=row['verdict'],names=sorted(matching)))
affected=set(prior['current_conservative_affected_CLOSED_rows'])|({'TX1:136'}if hits else set());out=dict(prior)
out.update(prior_closed_impact=len(prior['current_conservative_affected_CLOSED_rows']),new_closed_impact_if_promoted=len(affected),current_conservative_affected_CLOSED_rows=sorted(affected),new_row_hits=hits,root=name,reachability_receipt=str(source),reachability_uncompressed_sha256=H(raw),method=p['impact_method'],gate_reachability_used=bool(paths),input_pins={n:H(gitraw(n))for n in ['evidence/emission-repro-20261110/NMH_names.py','evidence/emission-repro-20261110/NMH_INVENTORY.json','evidence/emission-repro2-20261110/NML_PROVENANCE.json']},no_row_reopened=True,bk='Carry historical lead status verbatim; re-extraction plus per-definition equality remains a release blocker; fresh136 emission gives provenance for its emitted body only, not the entire child closure.')
(E/'NNI_PROVENANCE.json').write_text(json.dumps(out,indent=1)+'\n');print(json.dumps(dict(affected=len(affected),new_matching_unresolved_blobs=len(hits),gate_reachability_used=bool(paths))))
