#!/usr/bin/env python3
"""Read/hash-only current source correspondence for unchanged Prefix/parser cuts."""
from pathlib import Path
import argparse,hashlib,importlib.util,json,subprocess
root=Path(__file__).resolve().parents[4];here=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
p=here/'prefix-aggregate-extraction-kit/extract.py'
spec=importlib.util.spec_from_file_location('prefix_exact_cut',p);mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
out=mod.outputs();fresh=json.loads(out['source-pins.json']);old=json.loads((p.parent/'source-pins.json').read_text())
assert out['lib.rs']==(p.parent/'lib.rs').read_bytes()
assert [(x['name'],x['path'],x['sha256']) for x in fresh['declaration_cuts']]==[(x['name'],x['path'],x['sha256']) for x in old['declaration_cuts']]
rev='0ff133effe7ee299186700c2a91a35d5548b0ca5'
for path,h in fresh['source_files'].items():
 assert sha(subprocess.check_output(['git','-C',str(root),'show',rev+':'+path]))==h
result={'source_revision':rev,'current_source_files':fresh['source_files'],'previous_source_files':old['source_files'],'all28_declaration_hashes_identical':True,'regenerated_kit_lib_byte_identical':True,'lib_sha256':sha(out['lib.rs']),'cut_generator_sha256':sha(p.read_bytes()),'cuts':fresh['declaration_cuts'],'scope':'Current Git source correspondence for the exact same28-cut kit input; no tool/kernel rerun or Rust/runtime theorem; old receipts remain historical.'}
arg=argparse.ArgumentParser();arg.add_argument('--check',action='store_true');args=arg.parse_args();dest=root/'docs/research/100bit-spend-path-20261013/design/J1-DIGEST32-UNCHANGED-CUTS-20261016.json';raw=(json.dumps(result,indent=2,sort_keys=True)+'\n').encode()
if args.check:assert dest.read_bytes()==raw
else:dest.write_bytes(raw)
print('PASS28 current source cuts; entire Prefix/parser kit lib byte-identical; no build')
