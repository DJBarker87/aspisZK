#!/usr/bin/env python3
"""FAILED codegen experiment composing actual SDK method contracts.
This emits isolated annotation-only SDK inputs and a proof harness, never
production edits. Kani cannot generate Arbitrary values for the foreign live
guard/error return types. No enclosing composition certificate exists.
"""
from pathlib import Path
import hashlib,json,subprocess,sys
R=Path(__file__).resolve().parents[2]
registry,parts,sdk,prefix=map(Path,sys.argv[1:5])
assert not sdk.exists() and not prefix.exists()
sdk.mkdir(parents=True)
sha=lambda b:hashlib.sha256(b).hexdigest()
original=(registry/'src/lib.rs').read_text();source=original;annotations={}
for mode in ['length','shared','exclusive']:
 p=parts/('sdk-account-info-'+mode+'-v1')
 meta=json.loads((p/'source-cut.json').read_text())
 assert meta['original_sdk_source_sha256']==sha(original.encode())
 assert sha((p/'src/lib.rs').read_bytes())==meta['annotated_sdk_source_sha256']
 annotation=meta['annotation'];annotations[mode]=annotation
 assert (p/'src/lib.rs').read_text().replace(annotation,'')==original
 needle='    pub fn '+meta['method']+'('
 assert source.count(needle)==1;source=source.replace(needle,annotation+needle)
for name in ['Cargo.toml','Cargo.toml.orig','src/lib.rs','src/debug_account_data.rs']:
 p=sdk/name;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes((registry/name).read_bytes())
(sdk/'src/lib.rs').write_text(source)
stripped=source
for annotation in annotations.values():stripped=stripped.replace(annotation,'')
assert stripped==original
(sdk/'source-cut.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',original_sdk_source_sha256=sha(original.encode()),annotated_sdk_source_sha256=sha(source.encode()),annotations=annotations,strip_annotations_restores_exact_original=True,qualification=__doc__,remaining='Standalone actual-method checks exist for each identical method body/annotation. A coherent replay against this combined SDK source and actual enclosing native composition are still required; no method or whole-source closure follows from generation.'),indent=2)+'\n')
subprocess.run(['python3',str(R/'tools/s126-sdk-modular-20261021/prepare-sdk-shared-prefix.py'),str(prefix),'unreachable-cuts','exact-vec'],check=True)
p=prefix/'src/lib.rs';text=p.read_text();needle='#[kani::proof_for_contract(native_prefix)] #[kani::unwind(48)]'
assert text.count(needle)==1
text=text.replace(needle,needle+'\n'+''.join('#[kani::stub_verified(AccountInfo::'+method+')]\n' for method in ['try_data_len','try_borrow_data','try_borrow_mut_data']))
leaf_sources={}
for mode in ['length','shared','exclusive']:
 leaf=(parts/('sdk-live-'+mode+'-v1')/'src/lib.rs').read_text()
 begin=leaf.index('#[kani::proof_for_contract(')
 body=leaf[begin:leaf.rfind('\n}')].replace('fn actual_sdk_live_contract()', 'fn sdk_'+mode+'_contract()')
 assert body.count('fn sdk_'+mode+'_contract()')==1
 leaf_sources[mode]=sha(leaf.encode())
 end=text.rfind('\n}')
 text=text[:end]+'\n'+body+'\n'+text[end:]
p.write_text(text)
p=prefix/'Cargo.toml';p.write_text(p.read_text()+'\n[patch.crates-io]\nsolana-account-info={path="/home/dombarker/project-offloads/s126-real-sdk-20261021/'+sdk.name+'"}\n')
p=prefix/'source-cut.json';m=json.loads(p.read_text());m.update(source_sha256=sha(text.encode()),annotated_sdk_source_sha256=sha(source.encode()),sdk_source_original_sha256=sha(original.encode()),registered_leaf_harness_source_pins=leaf_sources,sdk_contract_composition='All three actual AccountInfo method calls use stub_verified contracts with exact status/counter/live-guard pointer postconditions and checked counter-only write frames. Their SDK method bodies remain original bytes; source/destination and live guard layouts are not replaced by an owned shadow. The actual native body, same-allocation borrowed reference, all aliases/metadata/Rc domains and explicit decoder-error phase cut remain. All method checks and parent proof/verified-stub implementation evidence are required.')
p.write_text(json.dumps(m,indent=2)+'\n')
