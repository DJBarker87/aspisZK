"""Check retained sources, native verdicts, frozen graphs and accepted Lean receipts."""
from pathlib import Path
import json,hashlib,lzma,re
E=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
def source(a,name):
 idx=json.loads((E/a/'SOURCE_INDEX.json').read_text());r=idx[name]
 b=lzma.decompress((E/r['payload']).read_bytes());assert sha(b)==r['sha256'];return b.decode()
def erase_cfg(s,flag):
 marker='if cfg!('+flag+')'
 while marker in s:
  start=s.index(marker);begin=s.index('{',start);depth=1;end=begin+1
  while depth:
   if s[end]=='{':depth+=1
   if s[end]=='}':depth-=1
   end+=1
  s=s[:start]+s[end:]
 return s
mod='NIW_src/crates/aspis-r1-cost-probe/src/NIW_boundary.rs'
x=source('NIW_K002',mod);y=source('NIW_K004',mod)
y=y.split('// Frozen verifier.rs finish_relation NEW port',1)[0]
assert erase_cfg(x,'NIW_corrupt').strip()==erase_cfg(y,'NIW_corrupt').strip()
x=source('NIW_K006',mod);y=source('NIW_K008',mod)
# The added control branch is erased under the passing configuration. Comments
# are outside semantics; this is a byte footprint check, not Rust verification.
clean=lambda s:re.sub(r'\s+','',re.sub(r'//[^\n]*','',erase_cfg(s,'NIW_mask_wrong')))
assert clean(x)==clean(y)
assert source('NIW_K009',mod)==source('NIW_K010',mod)
positives=['NIW_K002','NIW_K006','NIW_K009'];controls=['NIW_K004','NIW_K008','NIW_K010']
for a in [f'NIW_K{i:03}'for i in range(1,11)]:
 g=json.loads((E/(a+'-graph-check.json')).read_text());assert g['graph_matches_frozen']
 lock=json.loads((E/(a+'-lock-check.json')).read_text());assert lock['unchanged']
 assert lock['before']==lock['after']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
 cfg=json.loads((E/(a+'.json')).read_text());assert cfg['env']['CARGO_NET_OFFLINE']=='true'
 assert cfg['env']['CARGO_TARGET_DIR'].endswith('/codex-cx-slice-d-pair7-20261107/NIW_target')
 admission=json.loads((E/(a+'-admission.json')).read_text());assert admission['exit']==0 and admission['reservation']['allowed'] is True
for a in positives:
 t=(E/a/'stdout.log').read_text();assert 'VERIFICATION:- SUCCESSFUL' in t
for a in controls:
 t=(E/a/'stdout.log').read_text();assert 'Failed Checks: assertion failed:' in t and 'VERIFICATION:- FAILED' in t and 'CBMC timed out' not in t
accepted={}
for p in sorted(E.glob('NIW_L[0-9][0-9][0-9]/receipt.json')):
 r=json.loads(p.read_text())
 if r['exit_status']==0 and r['kind']=='lean' and (E/(r['module']+'.lean')).exists():
  h=sha((E/(r['module']+'.lean')).read_bytes())
  archived=p.parent/'sources/NIW_generated'/ (r['module']+'.lean')
  if archived.exists() and sha(archived.read_bytes())==h:accepted[r['module']]=r['attempt']
semantic=[p for p in E.glob('NIW_*.lean')if p.stem not in ['NIW_Driver','NIW_ProofDriver','NIW_COMBINED_IMPORT']]
for p in semantic:
 assert p.stem in accepted,p.stem
 assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b',p.read_text()),p
 t=(E/accepted[p.stem]/'stdout.log').read_text();assert 'sorryAx' not in t
 names=re.findall(r'^#print axioms (\S+)',p.read_text(),re.M)
 assert len(re.findall('depends on axioms:|does not depend on any axioms',t))==len(names)
if (E/'NIW_RETENTION.json').exists():
 retained=json.loads((E/'NIW_RETENTION.json').read_text());actual=retained['closure_files']
 for module,a in accepted.items():
  r=json.loads((E/a/'receipt.json').read_text())
  for path,expected in r['deps_fingerprint']['selected_objects'].items():
   if '/NIW_objects/NIW_' in path and path.endswith('.olean'):
    assert actual[path]['sha256']==expected['sha256'],(a,module,path,'stale imported NIW object')
result=dict(status='PASS',positive_control_pairs=list(zip(positives,controls)),unchanged_passing_body_checks=['K002/K004 cfg-erased same stage','K006/K008 added inverted-control branch unreachable in positive','K009/K010 identical source, control flag only'],frozen_graph_checks=10,accepted_sources=accepted,scope='Retained local cut/Lean source validation only; pair and finish remain OPEN',quarantined=[],suspended=[])
(E/'NIW_VALIDATION.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(dict(status='PASS',native_pairs=3,lean_modules=len(semantic))))
