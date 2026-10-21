#!/usr/bin/env python3
from pathlib import Path
import hashlib,json
p=Path(__file__).resolve().parent;m=json.loads((p/'manifest.json').read_text())
def sha(x):return hashlib.sha256(Path(x).read_bytes()).hexdigest()
for entry in m['direct_imports']:
 if sha(entry['source_path'])!=entry['source_sha256']:raise SystemExit('source mismatch '+entry['module'])
 if sha(entry['object_path'])!=entry['object_sha256']:raise SystemExit('object mismatch '+entry['module'])
g=Path(m['generated_v10_body']['path']).read_text()
cut=Path(m['direct_imports'][0]['source_path']).read_text()
if 'wideLimbCount' in g:raise SystemExit('generated V10 Funs unexpectedly mentions wideLimbCount')
start=cut.index('def literalV10Helper');end=cut.index('theorem literal_helper_eq_factored',start)
if 'wideLimbCount' in cut[start:end]:raise SystemExit('literal helper cut unexpectedly mentions wideLimbCount')
if sha(p/'sources/S4V10CountSlotIrrelevanceV1.lean')!=m['source']['sha256']:raise SystemExit('proof source mismatch')
print('PASS: pinned helper/outer and absence of wideLimbCount in the literal source cut')
