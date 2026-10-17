#!/usr/bin/env python3
"""Read/hash-only recorded-experiment component verification."""
from pathlib import Path
import hashlib,json,re,tarfile
ROOT=Path(__file__).resolve().parents[5];E=ROOT/'docs/research/100bit-spend-path-20261013/evidence/c2-recorded-experiment-20261017'
sha=lambda b:hashlib.sha256(b).hexdigest()
def main():
 audit=ROOT/'docs/research/100bit-spend-path-20261013/evidence/c2-historical-context-20261017/audit.json'
 assert sha(audit.read_bytes())=='d599abdfd7ca2ebd44a9b24e111596bf13d94b47f089912b6bd4b5de1ee973e8'
 assert json.loads(audit.read_text())['classification']=='HISTORICAL_CONTEXT_ONLY'
 members=json.loads((E/'recorded-members.json').read_text())
 with tarfile.open(E/'recorded-experiment.tar.gz') as tf:files={m.name:tf.extractfile(m).read() for m in tf.getmembers() if m.isfile()}
 assert set(files)==set(members)
 for n,b in files.items():assert sha(b)==members[n]['sha256'] and len(b)==members[n]['bytes'],n
 r=json.loads(files['runs/recorded-a/receipt.json']);assert r['target']=='C2RecordedExperimentConstruction' and r['exit_status']==0
 assert r['source_revision']=='6bd624b39' and r['external_lean_overlap']==[]
 assert r['limits']=={'memory.high':str(6*2**30),'memory.max':str(8*2**30),'memory.swap.max':'0'}
 assert r['reservation']['total_memory_max_bytes']<r['reservation']['safe_limit_bytes']
 assert r['process_swaps']==0 and r['cgroup_swap_current']=='0'
 source=files['runs/recorded-a/source.lean'];assert sha(source)==r['source_sha256']
 assert source==(ROOT/'docs/research/100bit-spend-path-20261013/lean/C2RecordedExperimentConstruction.lean').read_bytes()
 assert sha(files['objects/C2RecordedExperimentConstruction.olean'])==r['olean_sha256']
 log=files['runs/recorded-a/lean.log'].decode();reports=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",log)
 assert len(reports)==4 and 'sorryAx' not in log and 'error:' not in log
 for _,xs in reports:assert set(x.strip() for x in xs.split(','))=={'propext','Classical.choice','Quot.sound'}
 print(json.dumps({'status':'PASS','reports':4,'result_context':'HISTORICAL_CONTEXT_ONLY','current_accepted_semantic_model_results':0,'actual_Rust_execution_bridge':'OPEN','full_prover_verifier_witness_supplied':False,'archive_sha256':sha((E/'recorded-experiment.tar.gz').read_bytes())},sort_keys=True))
if __name__=='__main__':main()
