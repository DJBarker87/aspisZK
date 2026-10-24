"""Read-only source/receipt association and cumulative budget; no jobs launched."""
from pathlib import Path
import hashlib,json,re,subprocess
R=Path(__file__).resolve().parents[3]
D=Path(__file__).resolve().parent
E=R/'docs/research/100bit-spend-path-20261013/evidence/prover-rw-20261023/native-entropy'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
rows=[]

def metric(text,label):
    m=re.search(re.escape(label)+r':\s*(\d+)',text)
    return int(m[1]) if m else None

for a in range(13,25):
    p=E/f'extraction{a:03d}/receipt.json'
    x=json.loads(p.read_text())
    barrier=json.loads((p.parent/'reservation-at-barrier.json').read_text())
    assert barrier['allowed'] and barrier['requested_bytes']==0
    assert barrier['projected_reserved_bytes']<55*2**30
    assert x['swaps']==0 and x['cgroup_swap_peak_bytes']==0
    assert x['limits']=={'memory.high':str(6*2**30),'memory.max':str(8*2**30),'memory.swap.max':'0','pids.max':'64'}
    rows.append(dict(kind='extraction',attempt=a,receipt=str(p.relative_to(E)),receipt_sha256=sha(p),
        command=x['target'],exit_status=x['exit_status'],wall_seconds=x['wall_seconds'],
        peak_rss_kib=x['peak_rss_kib'],swaps=x['swaps'],print_axioms=x['print_axioms'],
        source_revision=x['source_revision'],source_hashes_field='source_sha256',
        dependency_fingerprint=x['deps_fingerprint'],accepted_source_artifact=False))

env=json.loads((E/'lean-command-environment.json').read_text())
J='/home/dombarker/project-offloads/aspis-joint-20261019'
for a in range(11559,11563):
    p=E/f'lean/{a}-receipt.json'
    x=json.loads(p.read_text());t=x['time_log'];m=x['module']
    barrier=json.loads((p.parent/f'{a}-admission-barrier.json').read_text())
    assert barrier['allowed'] and barrier['requested_bytes']==0
    assert barrier['own_limits']=={'memory.high':str(5*2**30),'memory.max':str(7*2**30),'memory.swap.max':'0','pids.max':'64'}
    assert metric(t,'Swaps')==0
    assert sha(p.parent/f'{a}.lean.txt')==x['source_sha256']
    cmd=[env['LEAN'],'-j1','-M7000','-DElab.async=false','-R',J+'/sources',
         '-o',J+'/objects/'+m+'.olean',J+'/sources/'+m+'.lean']
    rows.append(dict(kind='lean',attempt=a,receipt=str(p.relative_to(E)),receipt_sha256=sha(p),
        command=cmd,LEAN_PATH=J+'/objects:'+env['LEAN_PATH'],exit_status=x['exit_status'],
        wall=t.split('Elapsed (wall clock) time (h:mm:ss or m:ss): ')[1].splitlines()[0],
        peak_rss_kib=metric(t,'Maximum resident set size (kbytes)'),swaps=0,
        source_revision=x['source_revision'],source_sha256=x['source_sha256'],
        dependency_fingerprint=x['deps_fingerprint'],print_axioms=x['print_axioms']))

provenance=json.loads((E/'baseline-provenance.json').read_text())
assert sha(D/'baseline-InterpStatements.ml.txt')==provenance['source_manifest']['src/interp/InterpStatements.ml']['sha256']
source_associations=[]
for a,file in [(13,'extract013.py.txt'),(14,'translate014-reconstructed.py.txt'),
    (15,'extract015.py.txt'),(16,'translate016.py.txt'),(17,'extract017.py.txt'),
    (18,'translate018.py.txt'),(19,'extract019.py.txt'),(20,'translate020.py.txt'),
    (21,'extract-drop.py'),(22,'translate-baseline.py')]:
    x=json.loads((E/f'extraction{a:03d}/receipt.json').read_text())
    original='tools/prover-rw-20261023/native-entropy/'+('extract-drop.py' if a%2 else 'translate-baseline.py')
    assert sha(D/file)==x['source_sha256'][original]
    source_associations.append(dict(attempt=a,driver=file,sha256=sha(D/file),matches_receipt=True))
for a,file in [(13,'source-v1.rs.txt'),(15,'source-v2.rs.txt'),(17,'source-v3.rs.txt'),(19,'source-v4.rs.txt'),(21,'lib.rs')]:
    x=json.loads((E/f'extraction{a:03d}/receipt.json').read_text())
    assert sha(D/'drop-probe'/file)==x['source_sha256']['tools/prover-rw-20261023/native-entropy/drop-probe/lib.rs']
    source_associations.append(dict(attempt=a,rust_source=file,sha256=sha(D/'drop-probe'/file),matches_receipt=True))

prior=E.parent/'rng-extractor/continuation005/ledger.json'
x=json.loads(prior.read_text())
assert (x['backend_build_used'],x['extraction_used'],x['lean_cumulative_used'],x['kani_cumulative_used'])==(7,12,219,44)
ledger=dict(schema='ProverRwNativeEntropy-ledger-v1',prior_ledger_sha256=sha(prior),
    backend_used=7,backend_ceiling=12,backend_remaining=5,
    extraction_used=24,extraction_ceiling=24,extraction_remaining=0,
    lean_used=223,lean_ceiling=260,lean_remaining=37,
    kani_used=44,kani_ceiling=60,kani_remaining=16,
    source_associations=source_associations,rows=rows,
    validation_scope='Native tiny tests pass. Baseline translations020/022 emit missing Drop effects;020 whole output fails Lean. No kernel-accepted source counterexample. Candidate007 rejects minimal and actual selected64 before output. Only structural type and library signature audit kernel-check; no new source simulation theorem.',
    stop='Extraction ceiling exhausted; no supported complete real cleanup/loan path. No native rewrite/provider installation or full manifest authorized/attempted in this packet.',
    reused='Prior local theorem packets, source/LLBC pins and baseline binary/source association only; no new ELF identity or baseline rebuild.')
(E/'ledger.json').write_text(json.dumps(ledger,indent=2)+'\n')
for p in E.rglob('*.json'):
    assert p.stat().st_size<=5_000_000,p
integrity={str(p.relative_to(R)):dict(sha256=sha(p),bytes=p.stat().st_size)
    for base in [D,E] for p in base.rglob('*') if p.is_file() and p.name!='integrity.json'
    and '__pycache__' not in p.parts and p.suffix!='.pyc'}
(E/'integrity.json').write_text(json.dumps(integrity,indent=2)+'\n')
print(json.dumps({k:v for k,v in ledger.items() if k not in ('rows','source_associations')}))
