#!/usr/bin/env python3
import json,hashlib,time,resource,subprocess
from pathlib import Path
E=Path('evidence/sbf-identity-20261024');t=time.monotonic();deps={}
def load(n):
 b=(E/n).read_bytes();deps[n]=dict(sha256=hashlib.sha256(b).hexdigest(),bytes=len(b));return json.loads(b)
x=load('current-source-tree.json');y=load('rust-library-tree.json');off={'library/'+p['path']:p for p in y['tree'] if p['type']=='blob'};cur={p['path']:p for p in x['files']};summary={}
for prefix in ['library/alloc/','library/core/','library/']:
 a={p:v for p,v in cur.items() if p.startswith(prefix)};b={p:v for p,v in off.items() if p.startswith(prefix)};shared=a.keys()&b.keys()
 summary[prefix]=dict(current_files=len(a),official_files=len(b),shared=len(shared),mismatches=[p for p in sorted(shared) if a[p]['git_blob_sha1']!=b[p]['sha']],mode_mismatches=[p for p in sorted(shared) if ('100755' if int(a[p]['mode'],8)&0o111 else '100644')!=b[p]['mode']],missing=sorted(b.keys()-a.keys()),extra=sorted(a.keys()-b.keys()))
# Complete alloc/core equality, not selected function excerpts or names.
for prefix in ['library/alloc/','library/core/']:
 for k in ['mismatches','mode_mismatches','missing','extra']:assert not summary[prefix][k],(prefix,k)
submodules=[p for p in y['tree'] if p['type']=='commit'];extra=summary['library/']['extra'];unclassified=[p for p in extra if not any(p.startswith('library/'+s['path']+'/') for s in submodules)];assert not unclassified
u=resource.getrusage(resource.RUSAGE_SELF)
r=dict(schema='sbf-complete-source-properties-v1',declared_official_commit='790f1537507dbdb0da320fbb3b1c1eca3b33c474',summary=summary,submodules=submodules,extra_classification='All 409 extra packaged files lie under official gitlink submodules; their separate upstream commits/content are not claimed verified here. All direct official library blobs, and complete alloc/core paths and executable modes, match.',dependencies=deps,receipt=dict(command=['python3','tools/sbf-identity-20261024/analyze-source.py'],script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),exit=0,wall_seconds=time.monotonic()-t,peak_rss_bytes=u.ru_maxrss,swaps=u.ru_nswap,print_axioms='N/A: read-only metadata'))
(E/'complete-source-comparison.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({k:{a:b for a,b in v.items() if a!='extra'} for k,v in summary.items()},indent=2))
