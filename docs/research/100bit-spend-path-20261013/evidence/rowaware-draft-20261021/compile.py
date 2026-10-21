#!/usr/bin/env python3
"""Focused local compilation, immutable receipts, shared lock, private objects."""
import hashlib,json,os,pathlib,re,subprocess,sys,time
R=pathlib.Path(__file__).resolve().parent
ROOT=pathlib.Path.cwd(); SRC=ROOT/'docs/research/100bit-spend-path-20261013/lean'
OBJ=pathlib.Path('/tmp/codex-cx-rowaware-draft-20261021-objects'); OBJ.mkdir(exist_ok=True)
base=json.loads((R.parent/'oracle-port-draft-20261021/OraclePortAcceptedContextC6-1/command.json').read_text())
paths=list(dict.fromkeys([str(OBJ),'/tmp/codex-cx-domsep-20261021-objects']+base['lean_path'].split(':')))
sha=lambda p:hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
m=sys.argv[1]; assert m.startswith('OraclePortRowAware')
src=SRC/(m+'.lean'); deps=[]
for im in re.findall(r'^import (\S+)',src.read_text(),re.M):
    p=next((pathlib.Path(d)/(im.replace('.','/')+'.olean') for d in paths if (pathlib.Path(d)/(im.replace('.','/')+'.olean')).exists()),None)
    assert p, 'missing '+im
    deps.append(dict(module=im,path=str(p),sha256=sha(p)))
fp=hashlib.sha256(json.dumps(deps,sort_keys=True).encode()).hexdigest(); ss=sha(src)
for p in R.glob(m+'-*/command.json'):
    old=json.loads(p.read_text()); assert (old['source_sha256'],old['deps_fingerprint'])!=(ss,fp),'unchanged rerun refused'
a=1+max([int(p.name.rsplit('-',1)[1]) for p in R.glob(m+'-*') if p.is_dir()] or [0])
lock=pathlib.Path('/tmp/aspis-local-lean.lock.d')
while True:
    try: lock.mkdir()
    except FileExistsError:
        ps=subprocess.run(['pgrep','-fl','lean'],capture_output=True,text=True).stdout
        if time.time()-lock.stat().st_mtime>1800 and not re.search(r'/bin/lean\b',ps): lock.rmdir()
        else: print('Waiting for local Lean lock',flush=True); time.sleep(15)
        continue
    ps=subprocess.run(['pgrep','-fl','lean'],capture_output=True,text=True).stdout
    if re.search(r'/bin/lean\b.*-M4400',ps): lock.rmdir(); time.sleep(15); continue
    break
try:
    out=R/f'{m}-{a}'; out.mkdir(); (out/'source.lean').write_bytes(src.read_bytes())
    argv=[base['argv'][0],'-j1','-M4400','-DElab.async=false','-R',str(SRC),'-o',str(OBJ/(m+'.olean')),str(src)]
    cmd=dict(module=m,attempt=a,argv=argv,lean_path=':'.join(paths),source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_sha256=ss,direct_imports=deps,deps_fingerprint=fp,gate_processes=ps)
    (out/'command.json').write_text(json.dumps(cmd,indent=2)+'\n')
    start=time.monotonic()
    with (out/'lean.log').open('w') as f:
        proc=subprocess.run(['/usr/bin/time','-l','-o',str(out/'time.log')]+argv,stdout=f,stderr=subprocess.STDOUT,env={**os.environ,'LEAN_PATH':':'.join(paths)})
    wall=time.monotonic()-start; log=(out/'lean.log').read_text(); tm=(out/'time.log').read_text()
    rss=re.search(r'(\d+)\s+maximum resident set size',tm); swap=re.search(r'(\d+)\s+swaps',tm)
    receipt={**cmd,'exit':proc.returncode,'wall_seconds':wall,'peak_rss_bytes':int(rss[1]) if rss else None,'swaps':int(swap[1]) if swap else None,'axioms':re.findall(r"^.*(?:depends on axioms|does not depend on any axioms).*?(?=\n[^ \]]|\Z)",log,re.M|re.S),'errors':log if proc.returncode else [],'time_log':tm}
    (out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    entries=[json.loads(p.read_text()) for p in sorted(R.glob('*/receipt.json'))]
    (R/'manifest.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',attempts=entries),indent=2)+'\n')
    print(log); print(json.dumps({k:receipt[k] for k in ['module','attempt','exit','wall_seconds','peak_rss_bytes','swaps']},indent=2))
finally: lock.rmdir()
sys.exit(proc.returncode)
