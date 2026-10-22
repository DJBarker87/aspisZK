from pathlib import Path
import hashlib,json
p=Path(__file__).resolve().parent
receipt=json.loads((p/'attempt/evidence/receipt.json').read_text())
source=p/'sources/S4SolanaDigestP3RegroupV1.lean'
assert hashlib.sha256(source.read_bytes()).hexdigest()==receipt['source_sha256_before']==receipt['source_sha256_after']
assert receipt['exit_status']==0 and receipt['process_swaps']==0
log=(p/'attempt/evidence/lean.log').read_text()
for name in ['opening_flatten_eq_source_absorb','p3_digest_regroup','p3_digest_regroup_r4']:
 assert f"'S4SolanaDigestP3RegroupV1.{name}' depends on axioms: [propext, Classical.choice, Quot.sound]" in log,name
for rel in ['sources/S4SolanaDigestP3RegroupV1.lean','README.md','direct-import-pins.json','attempt/evidence/receipt.json','attempt/evidence/lean.log']:
 assert (p/rel).is_file(),rel
for f in p.rglob('*'):
 if f.is_file(): assert f.suffix not in ['.olean','.ilean','.ir','.c','.o','.a'],f
pins=json.loads((p/'direct-import-pins.json').read_text())
for n,row in pins.items():
 sp=p/'sources'/row['source'];op=Path(row['object_path'])
 assert hashlib.sha256(sp.read_bytes()).hexdigest()==row['source_sha256'],n+' source'
 assert hashlib.sha256(op.read_bytes()).hexdigest()==row['object_sha256'],n+' object pin'
assert 'R4Transport2OpeningChain.framed payload' in source.read_text()
assert 'ValidatedRecord.framed' not in source.read_text()
print('PASS: source-only P3 regroup packet hashes, direct import pins, axioms and boundary checks')
