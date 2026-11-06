from pathlib import Path
import json,sys
E=Path(__file__).resolve().parent
B='/home/dombarker/project-offloads/codex-cx-claims2-20261108';T='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0'
a,target=sys.argv[1:];n='NKA_generated/'+target+'.lean';p=E/n;p.parent.mkdir(exist_ok=True);p.write_text((E/(target+'.lean')).read_text())
x=dict(attempt=a,kind='lean',module=target,sources=[n],env=dict(LEAN_SYSROOT=T,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',TMPDIR=B+'/NKA_tmp',LEAN_PATH=':'.join(json.loads((E/'NKA_PATHS.json').read_text()))),timeout=180,expected_time='one focused new module',command=[T+'/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-R','NKA_generated','-o','NKA_objects/'+target+'.olean',n])
if target in ['NKA_Driver','NKA_ProofDriver']:x['command']+=['-c','NKA_native/'+target+'.c']
(E/(a+'.json')).write_text(json.dumps(x,indent=2)+'\n')
