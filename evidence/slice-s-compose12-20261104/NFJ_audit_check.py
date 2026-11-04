"""Ax2 completeness, exact fixtures, same binary and raw graph outputs."""
from pathlib import Path
import json,hashlib,lzma,difflib
E=Path(__file__).resolve().parent;A=E.parent/'axaudit2-20261102'
sha=lambda b:hashlib.sha256(b).hexdigest()
def check(data=None,fixtures=None):
 d=json.loads((E/'NFJ_AUDIT.json').read_text()) if data is None else data
 f=json.loads((E/'NFJ_FIXTURES.json').read_text()) if fixtures is None else fixtures
 assert (E/'NFJ_WALKER.lean').read_bytes()==(A/'NEP_WALKER.lean').read_bytes()
 assert d['walker_byte_identical'] is True and d['walker_sha256']==sha((A/'NEP_WALKER.lean').read_bytes())
 assert d['status']=='PASS' and d['zero_unresolved'] is True
 assert d['uses']=='uses RuntimeMemcmp (ac), ADDED trust'
 roots=json.loads((E/'NFJ_AUDIT_ROOTS.json').read_text());assert len(roots)==len(set(roots))==88
 assert d['root_count']==len(d['results'])==88 and {r['root'] for r in d['results']}==set(roots)
 assert all(r['equal'] and r['walked_axioms']==r['collect_axioms'] and set(r['walked_axioms'])<={'propext','Classical.choice','Quot.sound'} for r in d['results'])
 assert len(d['print_axioms'])==88
 assert f['status']=='PASS_AX2_CONDITION_3' and len(f['fixtures'])==8
 assert [r['walked_axioms'] for r in f['fixtures']]==[['NEP_Planted.matchAx'],['NEP_Planted.privateAx'],['NEP_Planted.proofAx'],['NEP_Planted.auxAx'],[],[],[],[]]
 assert all(r['equal'] and r['walked_axioms']==r['collect_axioms'] for r in f['fixtures'])
 assert d['driver_binary_sha256']==f['driver_binary_sha256']
 for attempt in ['NFJ_L011','NFJ_L012']:
  r=json.loads((E/attempt/'receipt.json').read_text());cfg=json.loads((E/(attempt+'.json')).read_text())
  assert r['exit_status']==0 and r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
  assert r['deps_fingerprint']['selected_objects']['/home/dombarker/project-offloads/codex-cx-slice-s-compose12-20261104/NFJ_native/NFJ_Driver']['sha256']==d['driver_binary_sha256']
  assert r['source_hashes']['NFJ_generated/NFJ_Driver.lean']==sha((E/'NFJ_Driver.lean').read_bytes())
  ad=json.loads((E/(attempt+'-admission.json')).read_text());assert ad['exit']==0 and ad['reservation']['allowed'] is True
  assert not any(s in (E/attempt/'stdout.log').read_text() for s in ['NEP_FAILURE','missing reachable constant'])
 raw=lzma.decompress((E/'NFJ_REACHABLE.json.xz').read_bytes());assert sha(raw)==(E/'NFJ_REACHABLE.json.sha256').read_text().strip()
 reachable=json.loads(raw);assert len(reachable)==96
 for mode,items in [('final',d['results']),('fixtures',f['fixtures'])]:
  for result in items:
   key='NEP_'+mode+'_'+result['root']+'_REACHABLE.txt'
   assert len(reachable[key].splitlines())==result['reachable_constants']
 diff=''.join(difflib.unified_diff((A/'NEP_Driver.lean').read_text().splitlines(True),(E/'NFJ_Driver.lean').read_text().splitlines(True),fromfile='NEP_Driver.lean',tofile='NFJ_Driver.lean'))
 assert diff==(E/'NFJ_DRIVER.diff').read_text()
 for name in ['NEP_Planted.lean','NEP_Mutations.lean']:assert (E/'NFJ_imports'/name).read_bytes()==(A/name).read_bytes()
 link=json.loads((E/'NFJ_L010/receipt.json').read_text())
 assert all(sha((E/n).read_bytes())==h for n,h in link['source_hashes'].items())
 return True
if __name__=='__main__':print('PASS ax2: 88 complete roots, 8 fixtures, identical walker and driver binary' if check() else 'FAIL')
