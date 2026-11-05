"""Additive NIL validation; baseline graph/resource/feature checks retained."""
from pathlib import Path
import json,hashlib,lzma,re,sys,copy,subprocess,base64
E=Path(__file__).resolve().parent;ROOT=E.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
FROZEN=json.loads((ROOT/'evidence/extract-stage-20261106/NHR_STAGING_MANIFEST.json').read_text())['files']
def check(ad,rc,graph,lock):
 assert ad['exit']==0 and ad['reservation']['allowed'] is True,'admission'
 assert graph['graph_matches_frozen'] is True,'graph'
 assert graph['lock_sha256']==lock['before']==lock['after']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef' and lock['unchanged'] is True,'lock'
 argv=rc['command'];assert argv==['python3','NIL_gate.py',rc['attempt']+'.json']
 x=json.loads((E/(rc['attempt']+'.json')).read_text())
 assert x['env']['CARGO_NET_OFFLINE']=='true'
 assert x['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3'
 assert x['native_command'][x['native_command'].index('--harness-timeout')+1]=='90s'
 assert '--locked' not in x['native_command']
 assert rc['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'},'limits'
 assert graph.get('all_crate_features'),'complete feature graph'
 f={r['name']:set(r['features']) for r in graph['all_crate_features']}
 assert f['aspis-r1-cost-probe']=={'default','private-leaf-salts','optimized-terminal','program-build'},'deployed library features'
 assert f['aspis-core']=={'r0'},'deployed core features'
 statement={'pool-v1-kernel','r0','spend-dynamic-rate512','pool-v1-pair-forest-active-mask-basis-audit','pool-v1-pair-forest-binary-copy-weights-audit','pool-v1-pair-forest-copy-finish-dot-basis-audit','pool-v1-pair-forest-copy-pattern-basis-audit','pool-v1-pair-forest-copy-selector-tensor-basis-audit','pool-v1-pair-forest-copy-tag-dot-basis-audit','pool-v1-pair-forest-endpoint-selector-cache-audit','pool-v1-pair-forest-packed-digest-audit','pool-v1-pair-forest-packed-digest-selector-tensor-audit','pool-v1-pair-forest-packed-range-audit','pool-v1-pair-forest-pattern-window-audit','pool-v1-pair-forest-semantic-factor-audit'}
 assert f['aspis-statement']==statement,'deployed statement features'
 assert '--features' in x['native_command'] and x['native_command'][x['native_command'].index('--features')+1]=='private-leaf-salts,optimized-terminal,program-build'
 for n,pin in json.loads((E/rc['attempt']/'sources/NIL_SOURCE_PINS.json').read_text()).items():
  p=E/rc['attempt']/'sources/NIL_src'/n
  if p.exists():assert sha(p)==pin,('source',n)
  else:
   # Frozen payload is committed once; every modified input must remain archived.
   assert n in FROZEN and FROZEN[n]['sha256']==pin,('missing modified source',n)
   pre=json.loads((E/(rc['attempt']+'-source-check.json')).read_text())
   assert pre['files']>=len(FROZEN) and pre['errors']==[],('pre-run source check',n)
 return True
