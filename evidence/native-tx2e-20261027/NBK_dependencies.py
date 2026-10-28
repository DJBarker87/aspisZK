from pathlib import Path
import subprocess,json,sys,hashlib
E=Path(__file__).resolve().parent
plan=json.loads((E/(sys.argv[1] if len(sys.argv)>1 else 'NBK_MISSING_PREPARED_PLAN.json')).read_text())
assert not plan['unknown']
for n,(module,source) in enumerate(plan['missing'],int(sys.argv[2]) if len(sys.argv)>2 else 12):
 a=f'NBK_L{n:03}'
 assert not (E/a/'receipt.json').exists()
 p=Path(source);data=p.read_bytes()
 assert subprocess.check_output(['git','show','HEAD:'+source])==data,'unchanged dependency required'
 (E/(a+'-NBK_UNCHANGED.json')).write_text(json.dumps({'module':module,'source':source,'source_sha256':hashlib.sha256(data).hexdigest(),'unchanged_at_revision':subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),'destination_cache':'/home/dombarker/project-offloads/codex-cx-leaf-cache-20261027','initially_absent':True},indent=2)+'\n')
 r=subprocess.run(['python3',str(E/'NBK_build.py'),a,source,module])
 if r.returncode:sys.exit(r.returncode)
 rc=json.loads((E/a/'receipt.json').read_text())
 if rc['exit_status']:sys.exit(rc['exit_status'])
