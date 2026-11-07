from NND_formal import *
r=ssh('python3',f"from pathlib import Path;import json;print(json.dumps((Path({B!r})/'NND_native/NND_ProofDriver.c').read_text()))")
assert r.returncode==0,r.stderr
files={'NND_native/NND_ProofDriver.c':json.loads(r.stdout)}
for stem in ['NFA_WALKER','NFA_MemoryLimit']:
 files['NND_native/'+stem+'.c']=(E/'NND_reuse/NND_audit_support'/(stem+'.c')).read_text()
cmd=[json.loads((E/'NND_ENV.json').read_text())['env']['LEAN_SYSROOT']+'/bin/lake','env','leanc','-O3','-rdynamic','-o','NND_native/NND_ProofDriver',*files]
r=run(sys.argv[1],'link','NND_ProofDriver',command=cmd,extra=files)
sys.exit(r['exit_status'])
