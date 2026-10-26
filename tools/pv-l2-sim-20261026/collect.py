"""Collect existing Env-J launcher receipts; does not alter launch infrastructure."""
import hashlib,json,pathlib,re,subprocess,sys
root=pathlib.Path(__file__).resolve().parents[2]
ev=root/'evidence/pv-l2-sim-20261026'
host='dombarker@100.108.41.90'
T='/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence'
J='/home/dombarker/project-offloads/aspis-joint-20261019'
for a,m in (x.split(':') for x in sys.argv[1:]):
    d=ev/f'J{a}';d.mkdir(exist_ok=True)
    for name in ['out','time','sha']:
        p=subprocess.run(['ssh',host,f'cat {T}/{name}-{a}.'+('txt' if name=='sha' else 'log')],capture_output=True,check=True)
        (d/f'{name}.log').write_bytes(p.stdout)
    out=(d/'out.log').read_text();tm=(d/'time.log').read_text()
    src=root/f'docs/research/v8-r0-zk-20261009/lean/R1Z/{m}.lean'
    sha=(d/'sha.log').read_text().split()[0]
    deps={}
    for mod in re.findall(r'^import (\S+)',src.read_text(),re.M):
        remote=f'{J}/objects/'+mod.replace('.','/')+'.olean'
        p=subprocess.run(['ssh',host,f'sha256sum {remote}'],capture_output=True)
        deps[mod]=p.stdout.decode().split()[0] if p.returncode==0 else None
    if hashlib.sha256(src.read_bytes()).hexdigest()==sha:(d/'source.lean').write_bytes(src.read_bytes())
    r={'attempt':int(a),'target':'R1Z/'+m,'source_sha256':sha,'deps':deps,'deps_fingerprint':hashlib.sha256(json.dumps(deps,sort_keys=True).encode()).hexdigest(),'deps_timing':'collected after run; direct deps unchanged by this job','source_revision':subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip(),'source_revision_note':'committed baseline at collection; exact submitted source pinned separately','exit':int(re.search(r'^exit=(\d+)',out,re.M)[1]),'wall':re.search(r'Elapsed.*: (\S+)\s*$',tm,re.M)[1],'peak_rss_kib':int(re.search(r'Maximum resident.*: (\d+)',tm)[1]),'swaps':int(re.search(r'Swaps: (\d+)',tm)[1]),'axioms':re.findall(r"'[^']+' depends on axioms: \[[^\]]*\]",out,re.S),'scope':{'MemoryHigh':'6G','MemoryMax':'8G','MemorySwapMax':0,'TasksMax':128},'lean_memory_mb':7000}
    (d/'receipt.json').write_text(json.dumps(r,indent=2)+'\n')
    print(a,r['exit'],r['wall'],r['peak_rss_kib'])
