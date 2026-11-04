"""Strict read-only validators. No prover launches or writes to inherited evidence."""
from pathlib import Path
import json,hashlib,importlib.util,sys,re,shlex
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;R=E.parents[1]
J=lambda p:json.loads(p.read_text())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
LOCK='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
KMX='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
assert sha(R/'evidence/kani-mitig-20261028/KMX_copy_stubs.patch')==KMX

def native(k,expected):
 a=f'NGH_K{k:03}';r=J(E/a/'receipt.json');ad=J(E/(a+'-admission.json'))
 assert r['exit_status']==expected and ad['exit']==0 and ad['reservation']['allowed']is True
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}and int(r['swaps'])==0
 g=J(E/(a+'-graph-check.json'));lock=J(E/(a+'-lock-check.json'));sc=J(E/(a+'-source-check.json'))
 assert g['graph_matches_frozen']and lock['unchanged']and lock['before']==lock['after']==LOCK and not sc['errors']
 assert r['env']['CARGO_NET_OFFLINE']=='true'and r['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3'
 assert next(p['features']for p in g['selected_closure']if p['name']=='aspis-core')==['r0']
 text=(E/a/'stdout.log').read_text()
 assert 'VERIFICATION:- '+('FAILED'if expected else 'SUCCESSFUL')in text
 assert 'CBMC timed out'not in text
 if expected:assert re.search(r'\*\* 1 of \d+ failed',text)
 for path,h in r['source_hashes'].items():assert sha(E/a/'sources'/path)==h,(a,path)
 own=[p for p in (E/a/'sources/NGH_src/crates/aspis-core/src').glob('NGH_*.rs')]
 for p in own:
  src=p.read_text();assert not re.search(r'\bstatic\b',src.replace('// Exact frozen expression with the three field products externalized to LOCAL log.',''))
  assert 'Option<fn'not in src
 return r

def pair(a,b):
 x=native(a,0);y=native(b,1)
 assert x['source_hashes']==y['source_hashes']and x['module']==y['module']
 xp=shlex.split(x['env']['RUSTFLAGS']);yp=shlex.split(y['env']['RUSTFLAGS'])
 assert yp.count('NGH_invert')==1 and 'NGH_invert'not in xp
 i=yp.index('NGH_invert');assert i>0 and yp[i-1]=='--cfg'
 assert yp[:i-1]+yp[i+1:]==xp
 assert {k:v for k,v in x['env'].items()if k!='RUSTFLAGS'}=={k:v for k,v in y['env'].items()if k!='RUSTFLAGS'}
 return x,y

def copy_pair(a,b):
 x=native(a,0);y=native(b,1)
 assert x['source_hashes']==y['source_hashes']and x['env']==y['env']
 return x,y

def inherited():
 T=E.parent/'slice-d-field-20261104';p=T/'NFT_certify.py'
 spec=importlib.util.spec_from_file_location('NGH_inherited_NFT',p);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
 rows=[]
 for a,b in [(20,21),(24,25),(26,27),(28,29),(78,79),(80,81),(82,83),(84,85),(86,87),(88,89),(98,99)]:
  x,y=m.pair(a,b);rows.append(dict(positive=x['attempt'],control=y['attempt'],positive_sha256=sha(T/x['attempt']/'receipt.json'),control_sha256=sha(T/y['attempt']/'receipt.json')))
 for a,b in [(22,23),(30,31),(32,33)]:m.copy_pair(a,b)
 m.native(100,1)
 return dict(validator=str(p.relative_to(R)),validator_sha256=sha(p),pairs=rows)

def build():
 pair(2,3);native(4,0);native(5,0);native(6,1);native(7,1);copy_pair(8,9)
 pair(11,12);native(13,1);copy_pair(14,15);pair(17,18)
 pair(30,31);native(32,0);native(33,0);native(34,1);native(35,1);copy_pair(36,37)
 for k in range(30,38):
  r=J(E/f'NGH_K{k:03}'/'receipt.json');assert '-Cdebuginfo=2'in r['env']['RUSTFLAGS']
  command=J(E/f'NGH_K{k:03}.json')['native_command'];assert ['-Z','loop-contracts']==command[-2:]
 inherited_result=inherited()
 result=dict(status='PASS',own_native_groups=['array shape fidelity','array copy','QM square local call-log','QM wrong-argument control','QM copy','one arbitrary accumulation cell reference contract'],inherited=inherited_result,KMX_patch_sha256=KMX,excluded=['NGH_K001 own missing harness error','NGH_K010 timeout: no credit, never rerun','NGH_K016 precondition evaluation ordering failure'],helper_level_contracts_closed=False,quarantined=[],suspended=[])
 (E/'NGH_NATIVE_VALIDATION.json').write_text(json.dumps(result,indent=1)+'\n');print(json.dumps(dict(status='PASS',inherited_pairs=len(inherited_result['pairs']))))
if __name__=='__main__':build()
