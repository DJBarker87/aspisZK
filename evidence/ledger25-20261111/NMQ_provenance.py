"""Same NMH/NML conservative lexical impact method, adding candidate064."""
from pathlib import Path
import json,lzma,hashlib,subprocess,sys,collections
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;M=E.parent/'emission-repro-20261110';L=E.parent/'emission-repro2-20261110';Q=E.parent/'tx2-entry5-20261110'
sys.path.insert(0,str(M));from NMH_names import declarations
p=json.loads((L/'NML_PROVENANCE.json').read_text());inv=json.loads((M/'NMH_INVENTORY.json').read_text());blobs={b['blob']:b for b in inv['blobs']}
root='NMN_064.root';paths=list(E.glob('NMQ_NEP_*_'+root+'_REACHABLE.txt.xz'))
source=paths[0] if paths else Q/'NEP_proof0_NMN_064.root_REACHABLE.txt.xz'
raw=lzma.decompress(source.read_bytes());reach=set(raw.decode().splitlines());hits=[]
for b in p['blobs']:
 if b['verdict'] in ['REPRODUCED','REPRODUCED_FROM_ARCHIVE']:continue
 original=blobs[b['blob']];text=subprocess.check_output(['git','show',inv['revision']+':'+original['paths'][0]],text=True)
 names=declarations(text);matching={d['name']for d in names if d['name'] in reach}
 for d in names:
  if d['private']:matching.update(n for n in reach if n.startswith('_private.') and n.endswith('.'+d['name']))
 if matching:hits.append(dict(blob=b['blob'],verdict=b['verdict'],names=sorted(matching)))
old=set(p['conservative_affected_CLOSED_rows']);new=old|({'TX2:064'}if hits else set())
out=dict(status='UNRESOLVED_RELEASE_BLOCKER_NO_ROW_REOPENED',historical_verbatim='extraction provenance is unresolved (NMH_/NML_: 336 blobs, 18 reproduced, 317 not reproduced, 2 semantic diffs outside the canonical domain; conservative impact 561 CLOSED rows by name matching)',count_caveat='Required lead aggregate wording retained verbatim; NML final serialized verdict buckets are 317 NOT_REPRODUCED,17 REPRODUCED_FROM_ARCHIVE,2 DIFFERS_SEMANTIC. These provenance buckets are retained without relabelling.',prior_closed_impact=len(old),new_closed_impact_if_promoted=len(new),current_conservative_affected_CLOSED_rows=sorted(new),new_row_hits=hits,root=root,reachability_receipt=str(source),reachability_uncompressed_sha256=hashlib.sha256(raw).hexdigest(),method=p['impact_method'],rootless_unassessed=p['rootless_CLOSED_unassessed'],no_row_reopened=True,release_plan='Release-gate re-extraction campaign over every reached reference/frozen input, with fully recorded configurations, followed by per-definition Lean equality to the committed definitions or repointed bridges and replay. Any definition without equality keeps release claims conditional.',rulings=['bk','bk addendum'])
(E/'NMQ_PROVENANCE.json').write_text(json.dumps(out,indent=1)+'\n');print(json.dumps(dict(prior=len(old),new_if_promoted=len(new),new_row_matching_blobs=len(hits))))
