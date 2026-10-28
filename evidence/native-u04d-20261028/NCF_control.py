"""Own controller; unchanged imported admission and S2W runner, serial scopes."""
from pathlib import Path
import importlib.util,sys,json,subprocess,shlex,hashlib
E=Path(__file__).resolve().parent;P=E.parent/'native-u04c-20261028'
args=sys.argv[1:];sys.argv=['ncc','none']
s=importlib.util.spec_from_file_location('inherited',P/'NCC_native.py');m=importlib.util.module_from_spec(s);exec(compile((P/'NCC_native.py').read_text().replace('NCC_NATIVE_TRANSPORT','NCF_NATIVE_TRANSPORT'),str(P/'NCC_native.py'),'exec'),m.__dict__);m.E=E
if args[0]=='install':
 m.admit('NCF_INSTALL')
 src=(E/'NCF_slots.rs.txt').read_text()
 r=m.py(f'''from pathlib import Path
import hashlib,json,difflib
b=Path({m.B!r});p=b/'NBU_src/crates/aspis-statement/src/pool_v1/verifier_registry.rs';old=p.read_text();assert 'mod NCF_slots' not in old
new=old+'\\n#[cfg(kani)]\\nmod NCF_slots;\\n';p.write_text(new)
h=b/'NBU_src/crates/aspis-statement/src/pool_v1/NCF_slots.rs';h.write_text({src!r})
patch=''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/crates/aspis-statement/src/pool_v1/verifier_registry.rs',tofile='b/crates/aspis-statement/src/pool_v1/verifier_registry.rs'))+''.join(difflib.unified_diff([],h.read_text().splitlines(True),fromfile='/dev/null',tofile='b/crates/aspis-statement/src/pool_v1/NCF_slots.rs'))
print(json.dumps(dict(before=hashlib.sha256(old.encode()).hexdigest(),after=hashlib.sha256(new.encode()).hexdigest(),patch=patch)))''')
 assert r.returncode==0,r.stdout+r.stderr
 x=json.loads(r.stdout);(E/'NCF_harness.patch').write_text(x.pop('patch'));(E/'NCF_INSTALL.json').write_text(json.dumps(x,indent=2))
elif args[0]=='extend':
 m.admit('NCF_EXTEND')
 source=(E/'NCF_slots.rs.txt').read_text()+''.join((E/n).read_text() for n in args[1:])
 r=m.py('from pathlib import Path; import json,hashlib; b=Path('+repr(m.B)+'); p=b/"NBU_src/crates/aspis-statement/src/pool_v1/NCF_slots.rs"; old=p.read_text(); p.write_text('+repr(source)+'); print(json.dumps(dict(before=hashlib.sha256(old.encode()).hexdigest(),after=hashlib.sha256(p.read_bytes()).hexdigest())))')
 assert r.returncode==0,r.stdout+r.stderr
 (E/'NCF_EXTEND.json').write_text(r.stdout)
 (E/'NCF_stage2_slots.rs.txt').write_text(source)
elif args[0]=='repair_path':
 m.admit('NCF_REPAIR_PATH')
 r=m.py('from pathlib import Path; import json,hashlib; b=Path('+repr(m.B)+'); p=b/"NBU_src/crates/aspis-statement/src/pool_v1/verifier_registry.rs"; s=p.read_text(); assert s.endswith("#[cfg(kani)]\\nmod NCF_slots;\\n"); s=s.replace("#[cfg(kani)]\\nmod NCF_slots;", "#[cfg(kani)]\\n#[path = \\"NCF_slots.rs\\"]\\nmod NCF_slots;"); p.write_text(s); print(json.dumps(dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest())))')
 assert r.returncode==0,r.stdout+r.stderr
 (E/'NCF_REPAIR_PATH.json').write_text(r.stdout)
elif args[0]=='batch':
 start=int(args[1]);hs=args[2:];assert start+len(hs)-1<=70
 m.admit('NCF_BATCH'+str(start)+'_UPLOAD')
 base=json.loads((P/'NCC_K060.json').read_text());base.update(timeout=600,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip())
 base['sources']=[x for x in base['sources'] if x not in ['NCC_gate.py','NCC_frozen_graph.sha256']]+['NCF_gate.py','NCF_frozen_graph.sha256','NBU_src/crates/aspis-statement/src/pool_v1/NCF_slots.rs']
 base['env']['CARGO_TARGET_DIR']=m.B+'/NCF_target';base['env']['TMPDIR']=m.B+'/NCF_tmp'
 targets=[dict(attempt=f'NCF_K{i:03}',module=h,command=['python3','NCF_gate.py',f'NCF_K{i:03}',h]) for i,h in enumerate(hs,start)]
 name=f'NCF_BATCH{start}.json';files={n:(E/n).read_text() for n in ['NCF_gate.py','NCF_frozen_graph.sha256','NCF_batch_host.py']};files[name]=json.dumps(dict(base=base,targets=targets))
 r=m.py('from pathlib import Path; b=Path('+repr(m.B)+'); (b/"NCF_tmp").mkdir(exist_ok=True); files='+repr(files)+'; [(b/n).write_text(s) for n,s in files.items()]');assert r.returncode==0,r.stderr
 cmd='cd '+shlex.quote(m.B)+' && nohup python3 NCF_batch_host.py '+shlex.quote(name)+' > '+shlex.quote(name+'.host.log')+' 2>&1 < /dev/null &'
 r=m.ssh(cmd,submitted=True);(E/(name+'-submission.json')).write_text(json.dumps(dict(exit=r.returncode,stdout=r.stdout,stderr=r.stderr,command=cmd),indent=2));print(name,r.returncode)
elif args[0]=='lean':
 a,mod=args[1:];m.admit(a)
 source=Path('lean',mod+'.lean').read_text();(E/(a+'-source.lean.txt')).write_text(source)
 lib=json.loads((P/'NCC_LIBRARY_PIN.json').read_text())
 r=m.py('from pathlib import Path; import json,hashlib; lib='+repr(lib)+'; assert all(hashlib.sha256(Path(p).read_bytes()).hexdigest()==v["sha256"] for p,v in lib.items()); cache=Path("/home/dombarker/project-offloads/codex-cx-tx2codec-cache-20261028"); out={str(p):dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size) for p in cache.rglob("*") if p.is_file()}; print(json.dumps(dict(cache=out,library=lib)))')
 assert r.returncode==0,r.stdout+r.stderr
 pins=json.loads(r.stdout);(E/(a+'-object-pins.json')).write_text(json.dumps(pins,indent=2))
 base=json.loads((P/'NCC_L002.json').read_text());cache='/home/dombarker/project-offloads/codex-cx-tx2codec-cache-20261028'
 base.update(attempt=a,module=mod,sources=['NCF_generated/'+mod+'.lean'],source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip())
 base['command']=[x.replace('NCC_generated','NCF_generated').replace('NCC_ReuseAudit',mod) for x in base['command']]
 obj=cache+'/NCC_ReuseAudit.olean';base['deps_fingerprint']={'selected_objects':{'NCC_ReuseAudit':dict(path=obj,**pins['cache'][obj])},'Aeneas':'see '+a+'-object-pins.json','sha256':hashlib.sha256(json.dumps(pins,sort_keys=True).encode()).hexdigest()}
 base['env']['LEAN_PATH']=base['env']['LEAN_PATH']
 files={'NCF_generated/'+mod+'.lean':source,a+'.json':json.dumps(base,indent=2)}
 r=m.py('from pathlib import Path; b=Path('+repr(m.B)+'); files='+repr(files)+'; [(b/n).parent.mkdir(parents=True,exist_ok=True) for n in files]; [(b/n).write_text(s) for n,s in files.items()]');assert r.returncode==0,r.stderr
 r=m.ssh('cd '+shlex.quote(m.B)+' && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_run_host.py '+a+'.json',submitted=True)
 (E/(a+'-launcher.log')).write_text(r.stdout+r.stderr);print(a,r.returncode)
elif args[0]=='collect_batch':
 name=args[1]
 r=m.py('from pathlib import Path; import json; b=Path('+repr(m.B)+'); spec=json.loads((b/'+repr(name)+').read_text()); a=[x["attempt"] for x in spec["targets"]]; names=['+repr(name)+','+repr(name+'.status.json')+']+[n+suffix for n in a for suffix in ["/receipt.json","/stdout.log","/time.log","-graph.json","-reservation.json",".json"]]; print(json.dumps({n:(b/n).read_text() for n in names if (b/n).exists()}))');assert r.returncode==0,r.stderr
 for n,s in json.loads(r.stdout).items():p=E/n;p.parent.mkdir(exist_ok=True,parents=True);p.write_text(s)
 rows=[json.loads(p.read_text()) for p in sorted(E.glob('NCF_[KL]*/receipt.json'))]
 (E/'NCF_ATTEMPTS.jsonl').write_text(''.join(json.dumps(x)+'\n' for x in rows));print([(x['attempt'],x['exit_status']) for x in rows])
elif args[0]=='recover':
 a=args[1];r=m.py('from pathlib import Path; import json; b=Path('+repr(m.B)+'); names='+repr([a+'/receipt.json',a+'/stdout.log',a+'/time.log',a+'-graph.json',a+'-reservation.json',a+'.json'])+'; print(json.dumps({n:(b/n).read_text() for n in names if (b/n).exists()}))');assert r.returncode==0,r.stderr
 for n,s in json.loads(r.stdout).items():p=E/n;p.parent.mkdir(exist_ok=True,parents=True);p.write_text(s)
 if (E/a/'receipt.json').exists():
  x=json.loads((E/a/'receipt.json').read_text());print(a,x['exit_status'],x['wall_seconds']);p=E/'NCF_ATTEMPTS.jsonl';old=p.read_text();line=json.dumps(x)+'\n';p.write_text(old+line if not any(json.loads(l)['attempt']==a for l in old.splitlines()) else old)
else:raise ValueError(args)
