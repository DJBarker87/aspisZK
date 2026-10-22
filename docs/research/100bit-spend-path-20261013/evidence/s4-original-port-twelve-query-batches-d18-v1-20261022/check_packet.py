#!/usr/bin/env python3
from pathlib import Path
import hashlib, json, re, sys
root = Path(__file__).resolve().parent
manifest = json.loads((root / 'manifest.json').read_text())
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
errors=[]
for rel, expected in manifest['packet_files'].items():
    p=root/rel
    if not p.is_file(): errors.append(f'missing {rel}')
    elif sha(p)!=expected: errors.append(f'hash mismatch {rel}')
for rel in manifest['forbidden_binary_suffixes']:
    for p in root.rglob('*'):
        if p.is_file() and p.suffix.lower()==rel: errors.append(f'compiled/binary artifact present: {p.relative_to(root)}')
receipt=json.loads((root/'receipt.json').read_text())
if receipt.get('exit_status') != 0: errors.append('receipt is not successful')
if receipt.get('source_sha256') != manifest['source_sha256']: errors.append('receipt/source hash mismatch')
if receipt.get('object_sha256') != manifest['external_object']['sha256']: errors.append('receipt/object hash mismatch')
if receipt.get('process_swaps') != 0: errors.append('successful target did not report zero swaps')
log=(root/'lean.log').read_text()
reports=re.findall(r"'"+re.escape(manifest['source_module'])+r"' depends on axioms: \[(.*?)\]", log, re.S)
if len(reports)!=1: errors.append('missing or duplicate named axiom report')
elif set(re.findall(r'[A-Za-z][A-Za-z0-9_.]*', reports[0])) != set(manifest['axioms']): errors.append('named report does not match standard axioms')
if 'sorryAx' in log or 'error:' in log: errors.append('unsuccessful or nonstandard compiler log')
source=root/'source/S4OriginalPortTwelveQueryBatchesV1.lean'
if sha(source)!=manifest['source_sha256']: errors.append('source/receipt pin mismatch')
for pin in manifest['direct_imports']:
    p=Path(pin['path'])
    if p.is_file() and sha(p)!=pin['sha256']: errors.append('selected direct owner changed: '+pin['module'])
if errors:
    print('\n'.join(errors)); sys.exit(1)
print('PASS: source-only pins, actual named standard-axiom report and receipt verified')
