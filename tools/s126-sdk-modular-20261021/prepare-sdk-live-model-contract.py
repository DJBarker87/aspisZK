#!/usr/bin/env python3
"""Check an experimental real-guard reference against the actual method spec.

Separate satisfaction of a complete specification avoids a paired execution.
This is NOT equivalence until uniqueness/representation and enclosing use are
proved. Original actual SDK contracts remain independent checked obligations.
"""
from pathlib import Path
import json,hashlib,sys,runpy
R=Path(__file__).resolve().parents[2];out=Path(sys.argv[1]);mode=sys.argv[2];base=Path(sys.argv[3]);sdk=Path(sys.argv[4])
assert mode in ['length','shared','exclusive'];assert not out.exists()
(out/'src').mkdir(parents=True)
cut=json.loads((sdk/'source-cut.json').read_text());method=cut['method']
model=(R/'tools/s126-sdk-modular-20261021/sdk-live-models.rs').read_text()
associated='associated' in sys.argv[5:]
if associated:model=runpy.run_path(str(R/'tools/s126-sdk-modular-20261021/make-associated-sdk-model.py'))['associated'](model)
annotation=cut['annotation'].replace('self.data','account.data')
needle=('pub fn '+mode+'(' if mode=='length' else "pub fn "+mode+("<'b>(" if associated else "<'b,'a>("))
assert model.count(needle)==1;model=model.replace(needle,annotation+needle)
s=(base/'src/lib.rs').read_text();s=s.replace('use std::cell::Cell;','use std::cell::Cell;\nmod sdk_live_models;')
target='sdk_live_models::'+('Models::' if associated else '')+mode
s=s.replace('AccountInfo::'+method,target)
s=s.replace('let result=account.'+method+'();','let result='+target+'(&account);')
assert 'let result='+target in s
(out/'src/lib.rs').write_text(s);(out/'src/sdk_live_models.rs').write_text(model)
(out/'Cargo.toml').write_text('''[package]
name="PACKAGE"
version="0.0.0"
edition="2021"
[workspace]
[dependencies]
solana-program="=2.3.0"
[profile.release]
opt-level=3
overflow-checks=true
'''.replace('PACKAGE','aspis-s126-'+out.name))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
(out/'source-cut.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',mode=mode,method=method,source_sha256=sha(out/'src/lib.rs'),model_sha256=sha(out/'src/sdk_live_models.rs'),actual_sdk_contract_source_sha256=sha(sdk/'src/lib.rs'),actual_contract_annotation=cut['annotation'],model_contract_annotation=annotation,qualification=__doc__,remaining='All model and actual method properties, complete spec uniqueness in pinned ABI including live guard drop and pointer representation, external ordinary-stub transport, actual native caller/error/trace/state/runtime join. No equivalence or S2 closure follows from this unary model contract alone.'),indent=2)+'\n')
