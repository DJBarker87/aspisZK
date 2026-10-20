#!/usr/bin/env python3
from pathlib import Path
import hashlib, json
base = Path(__file__).resolve().parents[3] / 'evidence/s3-s9-current-repin-20261020/row-output-equation-v7-v1'
source_root = Path(__file__).resolve().parent / 'sources'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
checks = {
 'body': ('S3VariantRowBodyProbe.lean', 'body'),
 'totality': ('S3VariantRowLoopTotal.lean', 'totality'),
 'value': ('S3VariantRowBodyValue.lean', 'value'),
 'invariant': ('S3VariantRowAccumulatorInvariant.lean', 'invariant'),
 'formula': ('S3VariantRowPrefixFormula.lean', 'formula'),
 'current-bridge': ('S3VariantRowCurrentSourceBridge.lean', 'current-bridge'),
}
for _, (filename, phase) in checks.items():
    expected = json.loads((base/phase/'receipt.json').read_text())['source_sha256']
    actual = sha(source_root/filename)
    if actual != expected: raise SystemExit(f'{phase} source mismatch: {actual} != {expected}')
model_receipt = json.loads((base/'source-model-owner/receipt.json').read_text())
if sha(source_root/'S3S9CurrentSourceModel.lean') != model_receipt['source_sha256']:
    raise SystemExit('source-model source mismatch')
report={'status':'pass','targets':{phase:sha(source_root/filename) for filename,phase in checks.values()},'source_model_sha256':model_receipt['source_sha256']}
print(json.dumps(report,indent=2))
