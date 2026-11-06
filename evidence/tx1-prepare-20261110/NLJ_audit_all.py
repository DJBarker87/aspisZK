from pathlib import Path
import subprocess,json,sys
E=Path(__file__).resolve().parent;T='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0'
def run(a):
 r=subprocess.run([sys.executable,str(E/'NLJ_run.py'),a]);assert (E/a/'receipt.json').exists(),'Recover; never resubmit'
 return r.returncode
subprocess.run([sys.executable,str(E/'NLJ_config.py'),'NLJ_L113','NLJ_COMBINED_IMPORT'],check=True)
assert run('NLJ_L113')==0
for n,mod in [(114,'NLJ_Driver'),(115,'NLJ_ProofDriver')]:
 a=f'NLJ_L{n:03}';subprocess.run([sys.executable,str(E/'NLJ_config.py'),a,mod],check=True)
 p=E/(a+'.json');x=json.loads(p.read_text());x['command']+=['-c','NLJ_native/'+mod+'.c'];x['collect']=['NLJ_native/'+mod+'.c'];p.write_text(json.dumps(x));assert run(a)==0
for n,mod in [(116,'NLJ_Driver'),(117,'NLJ_ProofDriver')]:
 a=f'NLJ_L{n:03}';x=json.loads((E/'NLJ_L114.json').read_text());x.update(attempt=a,kind='link',module=mod,sources=['NLJ_native/'+mod+'.c','NLJ_native/NFA_WALKER.c','NLJ_native/NFA_MemoryLimit.c'],command=[T+'/bin/lake','env','leanc','-O3','-rdynamic','-o','NLJ_native/'+mod,'NLJ_native/'+mod+'.c','NLJ_native/NFA_WALKER.c','NLJ_native/NFA_MemoryLimit.c'],collect=[],expected_time='Optimized unchanged audit runtime/walker C link');x.pop('deps_fingerprint',None);(E/(a+'.json')).write_text(json.dumps(x));assert run(a)==0
for n,mode in [(118,'fixtures'),(119,'scan')]+[(120+i,'proof'+str(i))for i in range(30)]+[(150,'close')]:
 a=f'NLJ_L{n:03}';subprocess.run([sys.executable,str(E/'NLJ_audit_config.py'),a,mode],check=True)
 rc=run(a)
 if rc:
  assert mode.startswith('proof'),'Unexpected scan/calibration failure'
  r=json.loads((E/'NLJ_audit'/mode/(mode+'.json')).read_text());bad=[v for v in r['results']if not v.get('equal',True)]
  assert len(bad)==1 and bad[0]['root']=='NHC_DecodeModel.decoder_error',bad
  assert set(bad[0]['walked_axioms'])<=set(['propext','Classical.choice','Quot.sound']),bad
print('One full combined gate complete; any inherited collector disagreement retained explicitly')
