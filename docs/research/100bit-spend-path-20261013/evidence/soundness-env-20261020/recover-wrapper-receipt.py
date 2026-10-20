"""Read-only recovery of compiler evidence after a launcher rewrite incident.
Run only after the driver has stopped; never reruns Lean.
"""
from pathlib import Path
import json,hashlib,re
D=Path(__file__).resolve().parent;J=D.parent;O=J/'objects-S'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
a=6678;module='R1Line18Geometry'
stdout=(D/f'launcher-{a}.log').read_text();tl=(D/f'time-{a}.log').read_text();obj=O/(module+'.olean')
assert re.search(r'^exit=0$',stdout,re.M) and re.search(r'Exit status: 0',tl) and obj.exists()
assert "'AspisR1.storedLine18_radix4_geometry' depends on axioms:" in stdout
rows=[json.loads(l) for l in (D/'attempts.jsonl').read_text().splitlines()];old=next(r for r in rows if r['attempt']==a)
man=json.loads((D/'manifest-S.json').read_text());e=next(e for e in man['order'] if e['module']==module);mods={x['module'] for x in man['order']}
fp=hashlib.sha256(';'.join(f'{x}={sha(O/(x.replace(".","/")+".olean"))}' for x in sorted(e['imports']) if x in mods).encode()).hexdigest()[:16]
assert old['deps_fingerprint']==fp
assert sha(J/'sources-S'/(module+'.lean'))==old['source_sha256']
recovery={'attempt':a,'module':module,'reason':'Launcher was replaced while an existing shell was executing it. The original compiler completed successfully (captured stdout exit=0, GNU time Exit status 0, matching source/dependency fingerprint and object). Shell then re-read the replaced script, emitted ime: not found and a syntax error, and overwrote out-6678.log. No compiler rerun.','original_receipt':old,'corrupted_out_sha256':sha(D/f'out-{a}.log'),'captured_launcher_stdout_sha256':sha(D/f'launcher-{a}.log'),'time_sha256':sha(D/f'time-{a}.log'),'object_sha256':sha(obj),'source_sha256':old['source_sha256'],'deps_fingerprint':fp,'compiler_exit':0,'wrapper_exit':2}
(D/'wrapper-recovery-6678.json').write_text(json.dumps(recovery,indent=2)+'\n')
ax=[' '.join(x.split()) for x in re.findall(r"^('[^']+' depends on axioms: \[[^\]]*\])",stdout,re.M|re.S)]
for r in rows:
 if r['attempt']==a:r.update(exit=0,compiler_exit=0,wrapper_exit=2,status='current-compiled-recovered',axioms=ax,object_sha256=sha(obj),errors=[],recovery_receipt='wrapper-recovery-6678.json')
(D/'attempts.jsonl').write_text(''.join(json.dumps(r)+'\n' for r in rows))
rows=[json.loads(l) for l in (D/'status.jsonl').read_text().splitlines()]
for r in rows:
 if r.get('attempt')==a:r.update(exit=0,compiler_exit=0,wrapper_exit=2,status='current-compiled-recovered',axioms=ax,object_sha256=sha(obj),errors=[],recovery_receipt='wrapper-recovery-6678.json')
(D/'status.jsonl').write_text(''.join(json.dumps(r)+'\n' for r in rows))
print('Recovered compiler success without replay:',module,a)
