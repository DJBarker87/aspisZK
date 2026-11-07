"""Re-emit pinned core/statement with deployed compiler flags, copied build output."""
import pathlib,subprocess,json,hashlib,shutil,sys,os,time,lzma
B=pathlib.Path(__file__).resolve().parent;I=json.loads((B/'PCH_BUILD_INPUT.json').read_text());a=sys.argv[1];out=B/a;out.mkdir(exist_ok=False)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
old='/home/dombarker/project-offloads/codex-cx-lowering2-20261026/sbf-target-pool';rec=[]
assert shutil.disk_usage(B).free>=40_000_000_000
buildinputs=[]
for p in sorted(pathlib.Path(old).glob('sbpf-solana-solana/release/build/aspis-core-*/out/circle_tables.rs')):
 buildinputs.append(dict(source=str(p),sha256=sha(p),bytes=p.stat().st_size))
assert len({r['sha256'] for r in buildinputs})==1
od=B/'core-out';od.mkdir(exist_ok=True);shutil.copyfile(buildinputs[0]['source'],od/'circle_tables.rs')
for c in ['aspis_core','aspis_statement']:
 cmd=[]
 for x in I['commands'][c]:cmd.append(x.replace(old,str(B/'deps')))
 cmd[cmd.index('--out-dir')+1]=str(out)
 # Statement consumes exactly the freshly generated core metadata.
 if c=='aspis_statement':
  cmd=[x.replace(str(B/'deps/sbpf-solana-solana/release/deps/libaspis_core-268c35f57b2871a4.rmeta'),str(out/'libaspis_core-268c35f57b2871a4.rmeta')) for x in cmd]
 env=os.environ.copy();env.update(OUT_DIR=str(od),CARGO_NET_OFFLINE='true')
 t=time.monotonic()
 with (out/(c+'.stdout')).open('w') as o,(out/(c+'.stderr')).open('w') as e:r=subprocess.run(cmd,cwd=B/'src',env=env,stdout=o,stderr=e)
 rec.append(dict(crate=c,command=cmd,exit_status=r.returncode,wall_seconds=time.monotonic()-t))
 assert r.returncode==0,c
for p in out.iterdir():
 if p.suffix in ['.mir','.ll','.stdout','.stderr']:(B/(a+'_'+p.name+'.xz')).write_bytes(lzma.compress(p.read_bytes()))
artifacts=[dict(path=str(p),sha256=sha(p),bytes=p.stat().st_size) for p in out.iterdir() if p.is_file()]
(B/(a+'_DEPENDENCIES.json')).write_text(json.dumps(dict(build_inputs=buildinputs,commands=rec,artifacts=artifacts),indent=1))
print('Pinned SBF core and statement re-emitted')
