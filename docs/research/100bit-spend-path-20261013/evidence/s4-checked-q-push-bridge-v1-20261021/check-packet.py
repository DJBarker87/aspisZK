#!/usr/bin/env python3
from pathlib import Path
import hashlib, json, re, subprocess, sys
W=Path(__file__).resolve().parent
ROOT=W.parents[4]

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def require(ok,msg):
    if not ok: raise SystemExit('FAIL: '+msg)
manifest=json.loads((W/'manifest.json').read_text())
listed={x['path']:x for x in manifest['files']}
actual={str(p.relative_to(W)) for p in W.rglob('*') if p.is_file() and p.name!='manifest.json'}
require(set(listed)==actual,f'file manifest mismatch: missing={sorted(set(listed)-actual)} extra={sorted(actual-set(listed))}')
for path,item in listed.items():
    p=W/path
    require(p.is_file(),f'missing {path}')
    require(sha(p)==item['sha256'],f'hash mismatch {path}')
    require(p.stat().st_size==item['bytes'],f'size mismatch {path}')

# Candidate-only source patch and exhaustive differential harness are independently pinned.
candidate=ROOT/'docs/research/100bit-spend-path-20261013/lean-candidates/s4-checked-q-all-unrolled-candidate-v1-20261021'
res=subprocess.run([sys.executable,str(candidate/'check_candidate.py')],cwd=ROOT,text=True,capture_output=True)
require(res.returncode==0,'underlying candidate source checker failed: '+res.stdout+res.stderr)

# The frozen Rust source retains the exact checked_q call and only changes Q::from_limbs.
orig=W/'source-snapshot/fast_pairing.original.rs'; cand=W/'source-snapshot/fast_pairing.candidate.rs'
require(sha(orig)=='5a84d748e3ac495a664e6b476c0b91a4bfa47408e76661a2834726d40ff28ea0','baseline Rust input pin')
require(sha(cand)=='2cb96261cecfd766b5e1b45a585b74c5f59c20c6be4f41e806239e2786ca7313','candidate Rust input pin')
for text in (orig.read_text(),cand.read_text()):
    require('fn checked_q(k: QM31) -> Result<canonical::Q, ()>' in text,'checked_q source signature missing')
    require('canonical::Q::from_limbs(limbs_of(k)).ok_or(())' in text,'checked_q order/call changed')
raw=(W/'source-snapshot/generated-Funs.lean').read_text()
require(sha(W/'source-snapshot/generated-Funs.lean')=='261f6894cd30de9d72da7ed66de853456e6b14101e4a3ccb32c9c862f36fd47e','generated Funs source pin')
start=raw.index('def fast_pairing.checked_q')
block=raw[start:raw.index('\n\n/-',start+5)]
require('let a ← fast_pairing.limbs_of k' in block,'generated checked_q limbs call missing')
require('let o ← fast_pairing.canonical.Q.from_limbs a' in block,'generated checked_q from_limbs call missing')
require('core.option.Option.ok_or o ()' in block,'generated checked_q ok_or call missing')

lean=(W/'sources/CandidatePushCheckedQBridge.lean').read_text()
require('def checkedQCandidate' in lean,'adapter body missing')
body=lean[lean.index('def checkedQCandidate'):lean.index('\ntheorem checkedQCandidate_eq_concreteAll')]
require('AspisR1EbyKCheckedQAllParamV1.limbsOf k' in body,'adapter limbs call missing')
require('AspisR1CheckedQCandidateV1.Q.from_limbs a' in body,'adapter candidate call missing')
require('AspisR1EbyKCheckedQAllParamV1.optionOkOr o ()' in body,'adapter option conversion missing')
require('sorry' not in lean and 'axiom ' not in lean and 'native_decide' not in lean,'forbidden proof construct')
for n in ('checkedQCandidate_eq_concreteAll','pushWithCandidateCheckedQ_eq_concreteAll','candidate_push_eq_qraw_backend'):
    require(n in lean,f'missing theorem {n}')

# Verify exact imported-source owners and their producer receipts.
source_map=json.loads((W/'direct_import_source_map.json').read_text())
require(source_map['consumer']['source_sha256']==sha(W/'sources/CandidatePushCheckedQBridge.lean'),'consumer source map pin')
for name,row in source_map['direct_imports'].items():
    src=W/row['source_copy']; receipt=W/row['producer_receipt_copy']
    require(sha(src)==row['source_sha256'],f'import source mismatch: {name}')
    require(sha(receipt)==row['producer_receipt_sha256'],f'import receipt mismatch: {name}')
for name,row in source_map['transitive_owner_snapshots'].items():
    src=W/row['source_copy']; require(sha(src)==row['source_sha256'],f'transitive source mismatch: {name}')
    if 'producer_receipt_copy' in row:
        receipt=W/row['producer_receipt_copy']; require(sha(receipt)==row['producer_receipt_sha256'],f'transitive receipt mismatch: {name}')

receipt=json.loads((W/'evidence/receipt.json').read_text())
require(receipt['exit_status']==0 and receipt['object_retained_in_repository'] is False,'successful source-only result required')
require(receipt['source_sha256']==sha(W/'sources/CandidatePushCheckedQBridge.lean'),'compiled source pin')
require(receipt['object_sha256']==manifest['modules'][0]['object_sha256'],'object hash mismatch')
require(receipt['swap_bytes']==0,'swap must be zero')
require(receipt['axioms']==['propext','Classical.choice','Quot.sound'],'unexpected axioms')
log=(W/'evidence/lean.log').read_text()
require('sorryAx' not in log,'sorryAx present in audit')
for theorem in ('checkedQCandidate_eq_concreteAll','pushWithCandidateCheckedQ_eq_concreteAll','candidate_push_eq_qraw_backend'):
    require(f"AspisR1S4CandidatePushCheckedQBridgeV1.{theorem}' depends on axioms" in log,f'missing axioms audit for {theorem}')
print('PASS: exact candidate/checked_q source mapping, direct owner pins, full-result QRaw equation, source-only receipt, and standard axioms')
