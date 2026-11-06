from pathlib import Path
import subprocess,json,sys
E=Path(__file__).resolve().parent;T='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0'
def run(a):
 r=subprocess.run([sys.executable,str(E/'NLC_run.py'),a]);assert (E/a/'receipt.json').exists(),'Recover; never resubmit'
 return r.returncode
subprocess.run([sys.executable,str(E/'NLC_config.py'),'NLC_L110','NLC_COMBINED_IMPORT'],check=True)
assert run('NLC_L110')==0
for n,mod in [(111,'NLC_Driver'),(112,'NLC_ProofDriver')]:
 a=f'NLC_L{n:03}';subprocess.run([sys.executable,str(E/'NLC_config.py'),a,mod],check=True)
 p=E/(a+'.json');x=json.loads(p.read_text());x['command']+=['-c','NLC_native/'+mod+'.c'];x['collect']=['NLC_native/'+mod+'.c'];p.write_text(json.dumps(x));assert run(a)==0
for n,mod in [(113,'NLC_Driver'),(114,'NLC_ProofDriver')]:
 a=f'NLC_L{n:03}';x=json.loads((E/'NLC_L111.json').read_text());x.update(attempt=a,kind='link',module=mod,sources=['NLC_native/'+mod+'.c','NLC_native/NFA_WALKER.c','NLC_native/NFA_MemoryLimit.c'],command=[T+'/bin/lake','env','leanc','-O3','-rdynamic','-o','NLC_native/'+mod,'NLC_native/'+mod+'.c','NLC_native/NFA_WALKER.c','NLC_native/NFA_MemoryLimit.c'],collect=[],expected_time='Optimized unchanged audit runtime/walker C link');x.pop('deps_fingerprint',None);(E/(a+'.json')).write_text(json.dumps(x));assert run(a)==0
for n,mode in [(115,'fixtures'),(116,'scan')]+[(117+i,'proof'+str(i))for i in range(31)]+[(148,'close')]:
 a=f'NLC_L{n:03}';subprocess.run([sys.executable,str(E/'NLC_audit_config.py'),a,mode],check=True)
 rc=run(a)
 if rc:
  assert mode.startswith('proof'),'Unexpected scan/calibration failure'
  r=json.loads((E/'NLC_audit'/mode/(mode+'.json')).read_text());bad=[v for v in r['results']if not v.get('equal',True)]
  assert len(bad)==1 and bad[0]['root']=='NHC_DecodeModel.decoder_error',bad
  assert set(bad[0]['walked_axioms'])<=set(['propext','Classical.choice','Quot.sound']),bad
print('One full combined gate complete; any inherited collector disagreement retained explicitly')
