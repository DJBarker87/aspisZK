from pathlib import Path
import json,sys
E=Path(__file__).resolve().parent
B='/home/dombarker/project-offloads/codex-cx-claims-queryscan-20261108';T='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0'
a,target=sys.argv[1:];n='NJT_generated/'+target+'.lean';p=E/n;p.parent.mkdir(exist_ok=True);p.write_text((E/(target+'.lean')).read_text())
x=dict(attempt=a,kind='lean',module=target,sources=[n],env=dict(LEAN_SYSROOT=T,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',TMPDIR=B+'/NJT_tmp',LEAN_PATH=':'.join(json.loads((E/'NJT_PATHS.json').read_text()))),timeout=180,expected_time='one focused new module',command=[T+'/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-R','NJT_generated','-o','NJT_objects/'+target+'.olean',n])
if target in ['NJT_Driver','NJT_ProofDriver']:x['command']+=['-c','NJT_native/'+target+'.c']
(E/(a+'.json')).write_text(json.dumps(x,indent=2)+'\n')
