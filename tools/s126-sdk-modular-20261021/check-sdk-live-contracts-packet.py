#!/usr/bin/env python3
"""Check retained actual-method contracts; deliberately reject enclosing claims."""
from pathlib import Path
import hashlib,json,re,tomllib,runpy
R=Path(__file__).resolve().parents[2]
E=R/'docs/research/100bit-spend-path-20261013/evidence/s126-current-caller-20261021/sdk-live-contracts'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
load=lambda p:json.loads(p.read_text())
manifest=load(E/'manifest.json')
for name,digest in manifest['files'].items():assert sha(E/name)==digest,name
assert not any(p.suffix in ['.out','.rlib','.o','.llbc'] for p in E.rglob('*'))
original=(E/'original-sdk/src/lib.rs').read_text()
original_hash='6b59aba664bb70fda6e17bcc8cf6eb41fc0bc9d8bcbb797bd70c1b107809c29a'
assert hashlib.sha256(original.encode()).hexdigest()==original_hash
accepted=[]
for mode,method,checks in [('length','try_data_len',776),('shared','try_borrow_data',763),('exclusive','try_borrow_mut_data',763)]:
 tag=f'sdk-live-{mode}-join-v1';crate=E/'sources'/f'sdk-live-{mode}-v1';sdk=E/'sources'/f'sdk-account-info-{mode}-v1'
 cut=load(crate/'source-cut.json');inp=load(E/(tag+'-input.json'));receipt=load(E/'receipts'/tag/'receipt.json')
 assert cut['method']==method
 assert cut['harness_source_sha256']==inp['source_sha256']==sha(crate/'src/lib.rs')
 assert cut['annotated_sdk_source_sha256']==sha(sdk/'src/lib.rs')
 assert (sdk/'src/lib.rs').read_text().replace(cut['annotation'],'')==original
 for rel in ['Cargo.toml','Cargo.toml.orig','src/debug_account_data.rs']:
  assert sha(sdk/rel)==sha(E/'original-sdk'/rel)
 assert receipt['exit_status']==0 and receipt['swaps']==0
 assert receipt['limits']['memory.swap.max']=='0' and int(receipt['limits']['memory.max'])==8*1024**3
 assert inp['env']['CARGO_BUILD_JOBS']=='1' and '-C opt-level=3' in inp['env']['RUSTFLAGS']
 assert '--unwinding-assertions' in inp['command'] and '--only-codegen' not in inp['command']
 log=(E/'receipts'/tag/'stdout.log').read_text()
 assert f'0 of {checks} failed' in log and '3 of 3 cover properties satisfied' in log and 'VERIFICATION:- SUCCESSFUL' in log
 meta=load(E/'metadata'/mode/'harness-metadata.json')
 rows=[h for h in meta['proof_harnesses'] if h['pretty_name']=='proofs::actual_sdk_live_contract'];assert len(rows)==1
 row=rows[0];assert row['attributes']['kind']=={'ProofForContract':{'target_fn':'AccountInfo::'+method}}
 assert not row['attributes']['stubs'] and not row['attributes']['verified_stubs']
 audit=load(E/'receipts'/f'sdk-live-{mode}-properties-v1'/'property-audit.json')
 assert audit['proof_receipt_sha256']==sha(E/'receipts'/tag/'receipt.json')
 assert any(p.get('class')=='assigns' for p in audit['contract_properties'])
 assert audit['method']==method
 lock=tomllib.loads((crate/'Cargo.lock').read_text())
 assert any(p['name']=='solana-account-info' and p['version']=='2.3.0' for p in lock['package'])
 accepted.append(dict(target=tag,method=method,receipt_sha256=sha(E/'receipts'/tag/'receipt.json'),original_sdk_sha256=original_hash,axioms='N/A: bounded Rust/Kani method contract, no Lean theorem',wall_seconds=receipt['wall_seconds'],peak_rss_kib=receipt['peak_rss_kib'],swaps=receipt['swaps']))
assert load(E/'qualification.json')['accepted']==[r['target'] for r in accepted]
models=[]
if (E/'sources/sdk-live-model-contract-length-v2').is_dir():
 reference=runpy.run_path(str(R/'tools/s126-sdk-modular-20261021/make-associated-sdk-model.py'))['associated']((R/'tools/s126-sdk-modular-20261021/sdk-live-models.rs').read_text())
 norm=lambda s:re.sub(r'\s+','',s)
 for mode,checks in [('length',741),('shared',763),('exclusive',760)]:
  folder=f'sdk-live-model-contract-{mode}-v2';crate=E/'sources'/folder;tag=f'sdk-live-model-contract-{mode}-join-v2'
  cut=load(crate/'source-cut.json');inp=load(E/(tag+'-input.json'));receipt=load(E/'receipts'/tag/'receipt.json')
  assert cut['source_sha256']==inp['source_sha256']==sha(crate/'src/lib.rs')
  assert cut['model_sha256']==inp['crate_source_pins']['src/sdk_live_models.rs']==sha(crate/'src/sdk_live_models.rs')
  assert (crate/'src/sdk_live_models.rs').read_text().replace(cut['model_contract_annotation'],'')==reference
  original_cut=load(E/'sources'/f'sdk-account-info-{mode}-v1'/'source-cut.json')
  assert cut['actual_contract_annotation']==original_cut['annotation']
  assert norm(cut['model_contract_annotation'])==norm(cut['actual_contract_annotation'].replace('self.data','account.data'))
  assert receipt['exit_status']==0 and receipt['swaps']==0 and receipt['limits']['memory.swap.max']=='0'
  log=(E/'receipts'/tag/'stdout.log').read_text()
  assert f'0 of {checks} failed' in log and '3 of 3 cover properties satisfied' in log
  meta=load(E/'metadata'/folder/'harness-metadata.json');rows=[r for r in meta['proof_harnesses'] if r['pretty_name']=='proofs::actual_sdk_live_contract'];assert len(rows)==1
  row=rows[0];assert row['attributes']['kind']=={'ProofForContract':{'target_fn':'sdk_live_models::Models::'+mode}}
  assert not row['attributes']['stubs'] and not row['attributes']['verified_stubs']
  audit=load(E/'receipts'/f'sdk-live-model-contract-{mode}-properties-v2'/'property-audit.json')
  assert audit['proof_receipt_sha256']==sha(E/'receipts'/tag/'receipt.json')
  assert any(p.get('class')=='assigns' for p in audit['contract_properties'])
  models.append(dict(target=tag,receipt_sha256=sha(E/'receipts'/tag/'receipt.json'),wall_seconds=receipt['wall_seconds'],peak_rss_kib=receipt['peak_rss_kib'],qualification='Unary model contract only. Common-spec uniqueness, complete heap/ABI adequacy and actual caller transport remain unproved.'))
print(json.dumps(dict(accepted_actual_method_contracts=accepted,checked_model_contracts=models,qualification='Source-helper contracts only. No enclosing source/caller premise discharged; all model-pair and parent attempts excluded.'),indent=2))
