#!/usr/bin/env python3
"""One fail-fast corpus, each whole retry-owner case compared immediately."""
from pathlib import Path
import hashlib,json,subprocess,sys,time
R=Path(__file__).resolve().parents[2];H=R.parent
assert len(sys.argv)==4,'usage: corpus.py baseline-binary candidate-binary fresh-output-dir'
B=dict(zip(['baseline','candidate'],map(Path,sys.argv[1:3])));O=Path(sys.argv[3]);O.mkdir(exist_ok=False)
pins={k:dict(path=str(b),sha256=hashlib.sha256(b.read_bytes()).hexdigest(),bytes=b.stat().st_size) for k,b in B.items()}
(O/'binaries.json').write_text(json.dumps(pins,indent=2)+'\n')
completed=[];started=time.monotonic();review=started
for coin in range(1000,2000):
    # Functional gate only: two isolated processes, each with 16 fixed workers.
    # Together they stay below TasksMax=64 and the original 8 GiB memory cap.
    children=[]
    try:
        for kind in ['baseline','candidate']:
            out=O/f'{coin}-{kind}'
            children.append(subprocess.Popen([str(B[kind]),str(out),str(coin),'1','0']))
        for child in children:
            code=child.wait(timeout=600)
            if code:raise RuntimeError(f'Corpus child exited {code}')
    finally:
        for child in children:
            if child.poll() is None:child.terminate();child.wait(timeout=10)
    comparison=O/f'comparison-{coin}.json'
    subprocess.run(['python3',str(R/'tools/prover-rw-20261023/compare-corpus.py'),str(O/f'{coin}-baseline'),str(O/f'{coin}-candidate'),str(comparison)],check=True,stdout=subprocess.DEVNULL)
    result=json.loads(comparison.read_text())
    completed.append(dict(coin=coin,utc=time.time(),**{k:v for k,v in result.items() if k!='comparisons'}))
    summary=dict(required_pairs=1000,completed_pairs=len(completed),passed=all(r['passed'] for r in completed),complete=len(completed)==1000,fully_executed_proof_pairs=sum(r['fully_executed_proof_pairs'] for r in completed),rejected_prefix_pairs=sum(r['rejected_prefix_pairs'] for r in completed),cases=completed,workers_per_process=16,simultaneous_processes=2,scope='All cases call the complete retry owner. Five ordinary tape classes, one rejected-prefix class, four error classes; both variants in every class. Full supplied-oracle streams are a separate smoke gate; all corpus pairs compare actual worker events, callback/ledger-event order, ledger bytes, status, audit and full public/proof bytes.')
    (O/'progress.json').write_text(json.dumps(summary,indent=2)+'\n')
    print('CORPUS_PROGRESS',json.dumps({k:summary[k] for k in ['completed_pairs','passed','complete','fully_executed_proof_pairs','rejected_prefix_pairs']}),flush=True)
    if time.monotonic()-review>=600:
        print('RESOURCE_REVIEW: expected runtime is named P_R1 elimination in optimized binaries; cases continue to complete, original 6G/8G/no-swap cap retained; no cap increase.',flush=True)
        review=time.monotonic()
