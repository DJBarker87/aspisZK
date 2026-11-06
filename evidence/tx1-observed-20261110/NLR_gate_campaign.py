"""One final coherent campaign. Every entry is one freshly admitted scope."""
from pathlib import Path
import json,subprocess,sys
E=Path(__file__).resolve().parent;B='/home/dombarker/project-offloads/codex-cx-tx1-observed-20261110';T='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0'
def invoke(a):
 assert not (E/a/'receipt.json').exists(),'Never resubmit'
 return subprocess.run([sys.executable,str(E/'NLR_run.py'),a]).returncode
def config(a,m,c=False):
 subprocess.run([sys.executable,str(E/'NLR_config.py'),a,m],check=True)
 if c:
  p=E/(a+'.json');x=json.loads(p.read_text());x['command']+=['-c','NLR_native/'+m+'.c'];p.write_text(json.dumps(x))
# Manifest/source preflight is local read-only; it is not a proof scope.
subprocess.run([sys.executable,str(E/'NLR_validate.py')],check=True)
subprocess.run([sys.executable,str(E/'NLR_prepare_audit.py')],check=True)
config('NLR_L101','NLR_COMBINED_IMPORT');assert invoke('NLR_L101')==0
for a,m in [('NLR_L102','NLR_Driver'),('NLR_L103','NLR_ProofDriver')]:
 config(a,m,True);assert invoke(a)==0
for a,m in [('NLR_L104','NLR_Driver'),('NLR_L105','NLR_ProofDriver')]:
 x=dict(attempt=a,kind='link',module=m,sources=['NLR_native/'+m+'.c','NLR_native/NFA_WALKER.c','NLR_native/NFA_MemoryLimit.c'],command=[T+'/bin/lake','env','leanc','-O3','-rdynamic','-o','NLR_native/'+m,'NLR_native/'+m+'.c','NLR_native/NFA_WALKER.c','NLR_native/NFA_MemoryLimit.c'],env=dict(LEAN_SYSROOT=T,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',TMPDIR=B+'/NLR_tmp',CARGO_TARGET_DIR=B+'/NLR_target',LEAN_PATH=':'.join(json.loads((E/'NLR_PATHS.json').read_text()))),timeout=180,expected_time='Optimized link of unchanged audit walker and own root-list driver')
 (E/(a+'.json')).write_text(json.dumps(x));assert invoke(a)==0
for n,mode in [(106,'fixtures'),(107,'scan')]+[(108+j,'proof'+str(j))for j in range(30)]+[(138,'close')]:
 a=f'NLR_L{n:03d}';subprocess.run([sys.executable,str(E/'NLR_audit_config.py'),a,mode],check=True)
 rc=invoke(a)
 if mode.startswith('proof'):
  # Preserve actual nonzero known collector disagreements; raw verdict is audited below.
  assert (E/a/'receipt.json').exists()
  checked=json.loads((E/'NLR_audit'/mode/(mode+'.json')).read_text())
  idx=int(mode[5:]);expected=json.loads((E/'NLR_AUDIT_ROOTS.json').read_text())['groups'][idx]
  results=checked['results'];assert sorted(r['root']for r in results)==sorted(expected),(a,'incomplete raw coverage')
  assert all(set(r['walked_axioms'])<={'propext','Classical.choice','Quot.sound'}for r in results),(a,'nonstandard raw axiom')
  if rc:assert any(not r['equal']for r in results),(a,'unexpected raw audit failure')
 else:assert rc==0,(a,mode,rc)
print(json.dumps(dict(campaign='COMPLETE_THROUGH_L138',combined_imports=1,final_native_credit=0)),flush=True)
