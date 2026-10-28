from pathlib import Path
import subprocess,json,hashlib,shlex,time
E=Path('evidence/pv-batch2-20261027/batch2f');H='dombarker@100.108.41.90';D='/home/dombarker/project-offloads/codex-pv-batch2-20261027';j=json.loads((E/'BOX-DEFECT.json').read_text())['boundary_revision'];p=Path('crates/aspis-r1-cost-probe/src/prover.rs');rev=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip();events=[]
assert hashlib.sha256(subprocess.check_output(['git','show','HEAD:'+str(p)])).hexdigest()==j['new_source_sha256']
def call(args):
 for n in range(10):
  r=subprocess.run(args,capture_output=True,text=True);events.append(dict(command=args,exit=r.returncode,stdout=r.stdout,stderr=r.stderr))
  (E/'BOX-APPLY.json').write_text(json.dumps(dict(source_revision=rev,events=events),indent=2)+'\n')
  if r.returncode==0:return r.stdout
  if r.returncode!=255:raise SystemExit(r.stderr+r.stdout)
  time.sleep(60)
 raise SystemExit('ten transient transport failures')
code=f"from pathlib import Path;import hashlib; p=Path({D+'/candidate/src/'+str(p)!r}); h=hashlib.sha256(p.read_bytes()).hexdigest(); print(h); assert h=={j['old_source_sha256']!r}"
print(call(['ssh',H,'python3 -c '+shlex.quote(code)]).strip())
call(['scp','-q',str(p),H+':'+D+'/candidate/src/'+str(p)])
code=f"from pathlib import Path;import hashlib; p=Path({D+'/candidate/src/'+str(p)!r}); h=hashlib.sha256(p.read_bytes()).hexdigest(); print(h); assert h=={j['new_source_sha256']!r}; Path({D+'/candidate/source-revision.txt'!r}).write_text({rev!r}+'\\n')"
print(call(['ssh',H,'python3 -c '+shlex.quote(code)]).strip())
call(['scp','-q','tools/pv-batch2-20261027/batch2f-elfs.py',H+':'+D+'/batch2f-elfs.py'])
print('applied exact own prover delta; kernel/extractor unchanged')
