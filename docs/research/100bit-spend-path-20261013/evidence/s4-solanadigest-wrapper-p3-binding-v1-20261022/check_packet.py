#!/usr/bin/env python3
"""Verify the source-only SolanaDigest/P3 adapter packet and its frozen receipts."""
from pathlib import Path
import hashlib, json, re, subprocess

ROOT = Path(__file__).resolve().parent
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
def require(cond, msg):
    if not cond:
        raise SystemExit(f"FAIL: {msg}")

packet = json.loads((ROOT / 'packet.json').read_text())
lean = ROOT / 'sources/S4SolanaDigestWrapperP3BindingV1.lean'
types = ROOT / 'generated/AspisR1SolanaDigestWrapperCut/Types.lean'
funs = ROOT / 'generated/AspisR1SolanaDigestWrapperCut/Funs.lean'
llbc = ROOT / 'generated/DigestWrapper-v4.llbc'
template = ROOT / 'diagnostics/FunsExternal_Template.not-imported.lean'
require(sha(lean) == '3c47c7353f7d1e6c4d909ba693aec59b3f044ec730b42dc2ecdf2f4c1b5b162e', 'adapter source pin')
require(sha(types) == packet['extraction']['translated_types_sha256'], 'generated Types source pin')
require(sha(funs) == packet['extraction']['translated_funs_sha256'], 'generated Funs source pin')
require(sha(llbc) == packet['extraction']['llbc_sha256'], 'LLBC pin')
require(sha(template) == packet['extraction']['external_template_sha256'], 'diagnostic template pin')
require('axiom solana_sha256_hasher.hashv' in template.read_text(), 'diagnostic template must expose external axiom')
repo = Path('/Users/dominic/ZK')
for key in ('P3_source', 'CurrentCaller_Types_source'):
    row = packet['owners'][key]
    require(sha(repo / row['path']) == row['sha256'], f'{key} source owner pin')
for key in ('P3_object', 'CurrentCaller_Types_object', 'PublicPreparation_Types_object', 'Aeneas_object'):
    row = packet['owners'][key]
    require(sha(Path(row['path'])) == row['sha256'], f'{key} selected object pin')
profile = packet['owners']['P3_complete_profile']
require(sha(Path(profile['path'])) == profile['sha256'], 'selected P3 compile profile pin')
for row in json.loads((ROOT / 'imports/P3-direct-import-pins.json').read_text()).values():
    require(sha(Path(row['object_path'])) == row['object_sha256'], f"P3 direct import object pin: {row['source']}")
imports = re.findall(r'^\s*import\s+(\S+)', lean.read_text(), re.M)
require(imports == ['AspisR1SolanaDigestWrapperCut.Types', 'S4SolanaDigestP3RegroupV1', 'AspisR1CurrentCaller.Types'], f'unexpected imports: {imports}')
require(not packet['extraction']['external_template_imported'], 'external axiom template must not be imported')
for forbidden in ('.olean', '.ilean', '.o', '.a', '.so', '.dylib', '.rlib', '.rmeta', '.elf'):
    require(not list(ROOT.rglob(f'*{forbidden}')), f'binary/compiled file present: {forbidden}')

for phase, source_sha, object_sha in (
    ('generated-types', packet['lean_results']['generated_types']['source_sha256'], packet['lean_results']['generated_types']['object_sha256_not_included']),
    ('wrapper-binding', packet['lean_results']['wrapper_binding']['source_sha256'], packet['lean_results']['wrapper_binding']['object_sha256_not_included']),
):
    base = ROOT / 'attempt/evidence'
    receipt = json.loads((base / f'{phase}.receipt.json').read_text())
    command = json.loads((base / f'{phase}.command.json').read_text())
    require(receipt['exit_status'] == 0, f'{phase} exit status')
    require(receipt['source_sha256_before_after'] == source_sha, f'{phase} source receipt hash')
    require(receipt['object_sha256'] == object_sha, f'{phase} object receipt pin')
    require(command['source_sha256'] == source_sha, f'{phase} launch source pin')
    require(command['compiler_sha256'] == packet['lean_sha256'], f'{phase} compiler pin')
    require(receipt['process_swaps'] == 0, f'{phase} swap count')

log = (ROOT / 'attempt/evidence/wrapper-binding.log').read_text()
for theorem in ('p3_digest_method_eq_model', 'p3_public_record_eq_model', 'p3_current_record_eq_model'):
    require(f"S4SolanaDigestWrapperP3BindingV1.{theorem}' depends on axioms: [propext, Classical.choice, Quot.sound]" in log,
            f'missing or nonstandard named axiom audit for {theorem}')
require('sorryAx' not in log and 'admit' not in lean.read_text(), 'admitted proof detected')

subprocess.run(['python3', str(ROOT/'check-kit.py')], check=True, stdout=subprocess.DEVNULL)
subprocess.run(['python3', str(ROOT/'check-functionalized-adapter.py')], check=True, stdout=subprocess.DEVNULL)
subprocess.run(['python3', str(ROOT/'check-llbc.py'), str(llbc)], check=True, stdout=subprocess.DEVNULL)
print('PASS: source mapping, P3/current dictionary adapter, exact Lean receipts, standard named axioms, LLBC, and no binaries')
