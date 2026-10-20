#!/usr/bin/env python3
"""Read-only frozen-source/site and packet checks; never launches a build."""
import hashlib,json,pathlib,re,subprocess,sys
PACK=pathlib.Path(__file__).resolve().parent
ROOT=PACK.parents[4]
BASE=ROOT/'docs/research/100bit-spend-path-20261013'
def sha(b):return hashlib.sha256(b).hexdigest()
frozen=json.loads((BASE/'evidence/freeze-20261020/source-hashes.json').read_text())
bad=[p for p,h in frozen['files'].items() if sha((ROOT/p).read_bytes())!=h]
assert not bad,bad
source=BASE/'evidence/stage2-continuation-20261020/generated/AspisR1Stage2/Funs.lean'
s=source.read_text();lines=s.splitlines()
direct=[[i,l.strip()] for i,l in enumerate(lines,1) if '.digest hash ' in l]
assert [i for i,l in direct]==[688,695,713,2613,2625,2649]
external=[[i,l.strip()] for i,l in enumerate(lines,1) if 'aspis_core.state_only_private_merkle.private_leaf_hash_with_digest' in l or 'aspis_core.r0.merkle.parent_with_digest' in l]
assert [i for i,l in external]==[621,634,646,1096]
branch='codex/cx-tx1-finish-prep-20261020'
parked_path='docs/research/100bit-spend-path-20261013/lean/Tx1PrepCheckpointFacts.lean'
parked=subprocess.check_output(['git','show',branch+':'+parked_path],cwd=ROOT)
for name in ['checkpoint_writer_proof_digest','successful_writer_resume_share_proof_digest']:
 assert ('theorem '+name).encode() in parked
new=['RawDigestLogCarrier','RawTx2ResumeDigestCalls','RawTx2DigestLog','RawTx2CheckpointLink','RawTx1Tx2ConsistentLog']
for module in new:
 text=(BASE/'lean'/f'{module}.lean').read_text()
 assert not re.search(r'\b(sorry|axiom|admit|native_decide)\b|set_option\s+(maxRecDepth|maxHeartbeats)',text)
record={'base_revision':'8ced75478ded9fbac42ab4551e011e537cebd0ef','frozen_revision':frozen['source_revision'],'frozen_files_checked':len(frozen['files']),'generated_source':str(source.relative_to(ROOT)),'generated_sha256':sha(source.read_bytes()),'direct_sites':direct,'external_hash_boundaries':external,'coverage_status':'syntactic inventory checked; dynamic call completeness and external models remain named premises','parked_branch':branch,'parked_tip':subprocess.check_output(['git','rev-parse',branch],cwd=ROOT,text=True).strip(),'parked_module':parked_path,'parked_module_sha256':sha(parked),'parked_imported':False,'new_modules':{m:sha((BASE/'lean'/f'{m}.lean').read_bytes()) for m in new}}
out=PACK/'source-inventory.json'
if out.exists() and '--write' not in sys.argv:assert json.loads(out.read_text())==record
else:out.write_text(json.dumps(record,indent=2)+'\n')
print(f"Checked {len(frozen['files'])} frozen source pins, 6 direct sites, 4 external hash calls; parked source read with git show only.")
