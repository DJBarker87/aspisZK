"""Resolve stale local candidate ref explicitly; never recapture worker heads."""
import json,subprocess
from pathlib import Path
P=Path(__file__).resolve().parent;p=json.loads((P/'pins.json').read_text())
p.setdefault('local_candidate_ref',{'ref':p['refs']['rw'],'revision':p['revisions']['rw'],'disposition':'stale local ref from 2026-10-29; not the shared candidate branch head'})
p['refs']['rw']='refs/remotes/origin/codex/cx-prover-rw-20261023';p['revisions']['rw']=subprocess.check_output(['git','rev-parse',p['refs']['rw']]).decode().strip();p['candidate_resolution']='Shared candidate = existing origin tracking ref, d4ed1ba89f; local branch is stale. No fetch, reset, checkout or branch edit.'
(P/'pins.json').write_text(json.dumps(p,indent=1)+'\n')
from audit12 import *
manifest.update({x['ref']+':'+x['path']:x for x in json.loads((P/'manifest.json').read_text())})
# Preserve initial stale-ref reads as such, not evidence for the resolved candidate.
for key in list(manifest):
 if key.startswith('rw:'):
  z=manifest.pop(key);z['ref']='rw-local';manifest['rw-local:'+z['path']]=z
old=json.loads((B/'recount11/definition-audit11.json').read_text());new=json.loads((P/'definition-audit12.json').read_text())
for d,prior in zip(new,old):
 paths={s['path'] for s in d['sources']};d['sources']=[s for s in d['sources'] if s['ref']!='rw']
 for path in paths:
  if read('rw',path) is not None:
   z=dict(manifest['rw:'+path]);z['prior_identical']=any(s['path']==path and s['sha256']==z['sha256'] for s in prior['sources']);d['sources'].append(z)
 d['changed']=[z for z in d['sources'] if not z['prior_identical']]
(P/'definition-audit12.json').write_text(json.dumps(new,separators=(',',':'))+'\n')
for k in ['rw','uc','research']:
 for path in ['tools/r1-cost-probe/src/bin/devnet_spend/diagnostics.rs','tools/r1-cost-probe/src/bin/user_client/diagnostics.rs']:read(k,path)
save();print('resolved candidate',revs['rw'])
