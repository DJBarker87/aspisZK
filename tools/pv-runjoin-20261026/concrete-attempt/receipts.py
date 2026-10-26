from pathlib import Path
import json,hashlib,re,subprocess
out=Path('evidence/pv-runjoin-20261026/concrete-attempt')
base=Path('tools/pv-runjoin-20261026/concrete-attempt/native-fault')
revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
for attempt in ['01','02']:
    d=out/f'native-fault-{attempt}'
    old=attempt=='01'
    source=d if old else base
    names=['Cargo.toml','main.rs','selected.rs']
    pins={n:dict(sha256=hashlib.sha256((source/n).read_bytes()).hexdigest(),bytes=(source/n).stat().st_size) for n in names}
    phases={}
    for phase in ['build','run']:
        f=d/(phase+('.time' if old else '-02.time'))
        s=f.read_text()
        phases[phase]=dict(exit=int(re.search(r'Exit status: (\d+)',s)[1]),metrics=[v.strip() for v in s.splitlines() if any(k in v for k in ['Elapsed','Maximum resident','Swaps:'])])
    r=dict(target='literal frozen generate_for_mask_nonce source selection with real getrandom/zeroize and process-only seccomp EIO' if not old else 'EPERM setup rejected by dependency fallback behavior',source_revision=revision,source_was_uncommitted=True,source_pins=pins,phases=phases,command='systemd-run --user --scope --quiet -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 sh /home/dombarker/project-offloads/codex-pv-runjoin-20261026/native-fault/run.sh',build_command='cargo build --offline --release -j 4',print_axioms='N/A native source-helper observation; separate Lean receipts23404/23405',caps=dict(MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=64),kani_runs=0,proves_privacy_counterexample=False,scope='source helper only; no complete client/artifact/deployment claim')
    (d/'receipt.json').write_text(json.dumps(r,indent=2)+'\n')
for p in out.glob('receipt-*.json'):
    r=json.loads(p.read_text());r['source_was_uncommitted']=True
    p.write_text(json.dumps(r,indent=2)+'\n')
