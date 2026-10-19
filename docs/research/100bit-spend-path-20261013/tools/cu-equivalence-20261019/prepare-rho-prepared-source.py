#!/usr/bin/env python3
"""Reuse only exact Prepared.new source/body; share checked current carriers."""
from pathlib import Path
import argparse,hashlib,importlib.util,json,re,subprocess,tempfile
ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');a=ap.parse_args()
here=Path(__file__).resolve().parent;area=here.parents[1];repo=here.parents[4];sha=lambda b:hashlib.sha256(b).hexdigest()
spec=importlib.util.spec_from_file_location('cut',area/'tools/public-serializer-extraction-kit/extract.py');cut=importlib.util.module_from_spec(spec);spec.loader.exec_module(cut)
candidate='16a39d2a8a5124e25c787f2b9fcaf8449fb84611';identity=[]
reference=(here/'cu-gamma-input/fragments/new-prepare-candidate.rs').read_bytes()
for revision in [candidate+'^',candidate,'39c2971dd16c95858a4cfd2c9ae35da052eacfa9']:
 raw=subprocess.check_output(['git','-C',str(repo),'show',revision+':crates/aspis-r1-cost-probe/src/verifier.rs'])
 with tempfile.NamedTemporaryFile() as f:
  f.write(raw);f.flush();body,*_=cut.find_item(Path(f.name),'pub fn new<H:Digest32>')
 assert body==reference
 identity.append(dict(revision=revision,prepared_new_body_sha256=sha(body)))
original_input=here/'cu-gamma-input/lib.rs'
original_method,*_=cut.find_item(original_input,'pub fn gamma_new_new<H:Digest32>')
assert original_method==reference.replace(b'pub fn new<H:Digest32>',b'pub fn gamma_new_new<H:Digest32>',1)
receipt=json.loads((area/'evidence/cu-equivalence-20261019/cu-gamma-aeneas-prepared-b/receipt.json').read_text())
assert receipt['exit_status']==0
assert receipt['source_pins_sha256']==sha((here/'cu-gamma-input/source-pins.json').read_bytes())
original_pins=json.loads((here/'cu-gamma-input/source-pins.json').read_text())
for name,pin in original_pins['kit_files'].items():assert sha((here/'cu-gamma-input'/name).read_bytes())==pin,name
assert receipt['frontend_binary_sha256']=='4632746db1bf6c3953f2971078965a2a5a8ad6cf5f75636b46b397bc50c550b5'
def blocks(raw):
 header,*chunks=re.split(rb'(?m)(?=^/--)',raw);assert chunks and chunks[-1].endswith(b'end AspisR1CuGamma\n');chunks[-1]=chunks[-1][:-len(b'end AspisR1CuGamma\n')]
 result={}
 for chunk in chunks:
  m=re.search(rb'(?m)^(?:def\s+|def\s*\n\s*|structure\s+|inductive\s+)([\w.]+)',chunk);assert m
  result[m[1].decode()]=chunk
 return header,result
rawtypes=(here/'cu-gamma-generated/Types.lean').read_bytes();typeheader,types=blocks(rawtypes)
rawfuns=(here/'cu-gamma-generated/Funs.lean').read_bytes();funheader,funs=blocks(rawfuns)
rawpins=json.loads((here/'cu-gamma-emission-inputs.json').read_text());assert sha(rawtypes)==rawpins['Types.lean'] and sha(rawfuns)==rawpins['Funs.lean']
kept=['r1_wire.Challenges','r1_wire.SemanticTranscript','r1_semantic.Verified','verifier.View'];shared=['aspis_core.field.M31','aspis_core.field.CM31','aspis_core.field.QM31','aspis_core.circle.SecureCirclePoint','aspis_core.field.WideExact','transport.Variant','verifier.Prepared']
clean=lambda b:re.sub(rb'/--.*?-/',b'',b,flags=re.S).replace(b'@[discriminant isize]\n',b'').strip()
existing=(area/'lean/AspisR1RhoPowerTail/Types.lean').read_bytes()
for name in shared:assert clean(types[name]) in existing,name
# Both aliases share all fields; only the declaration-owner paths differ.
scalartypes=(area/'lean/AspisR1RhoScalarK/Types.lean').read_bytes()
assert clean(types['aspis_core.Digest32']).replace(b'aspis_core.Digest32',b'Digest32') in scalartypes
assert clean(types['transcript.Transcript']) in scalartypes
error=(area/'lean/AspisR1RhoInit/Types.lean').read_bytes();assert clean(types['verifier.Error']) in error
header=typeheader.replace(b'import Aeneas\n',b'import AspisR1RhoAccumulatorNew.Funs\nimport AspisR1RhoScalarK.Types\n').replace(b'namespace AspisR1CuGamma\n',b'namespace AspisR1RhoPowerTail\nabbrev aspis_core.Digest32 := AspisR1CuRho.Digest32\nabbrev transcript.Transcript := AspisR1CuRho.transcript.Transcript\n')
typesout=header+b''.join(types[n] for n in kept)+b'end AspisR1RhoPowerTail\n'
# The three shared source functions used by the caller are exact existing defs.
constructor=(area/'lean/AspisR1RhoAccumulatorNew/Funs.lean').read_bytes()
for name in ['aspis_core.field.WideExact.ZERO','transport.Variant.Insts.CoreCmpPartialEqVariant.eq','transport.Variant.folds']:assert clean(funs[name]) in constructor,name
fn='gamma_new.Prepared.gamma_new_new';selected=funs[fn]
header=funheader.replace(b'import AspisR1CuGamma.Types\n',b'import AspisR1RhoPrepared.Types\n').replace(b'import AspisR1CuGamma.FunsExternal\n',b'import AspisR1RhoPrepared.FunsExternal\n').replace(b'namespace AspisR1CuGamma\n',b'namespace AspisR1RhoPowerTail\nvariable [PreparedCommon] [AspisR1CuRho.ScalarKBlocks]\n')
header=header.replace(b'variable [Boundaries]\n',b'variable [PreparedCommon] [AspisR1CuRho.ScalarKBlocks]\n')
# Raw function bodies are selected from the raw generated output, not from a
# hand-written approximation or a modified optimization proof.
funsout=header+selected+b'end AspisR1RhoPowerTail\n'
outputs={'Types.lean':typesout,'Funs.lean':funsout}
for n,b in outputs.items():
 p=area/'lean/AspisR1RhoPrepared'/n
 if a.check:assert p.read_bytes()==b,n
 else:p.parent.mkdir(exist_ok=True);p.write_bytes(b)
meta=dict(source_identity=identity,original_input_sha256=sha(original_input.read_bytes()),original_prepared_declaration_sha256=sha(original_method),raw_emission_receipt='cu-gamma-aeneas-prepared-b',raw_types_sha256=sha(rawtypes),raw_funs_sha256=sha(rawfuns),selected_declaration=fn,raw_selected_declaration_sha256=sha(selected),new_types=kept,shared_identical_carriers=shared,alias_identical_carriers=['aspis_core.Digest32','transcript.Transcript','verifier.Error'],promoted={n:sha(b) for n,b in outputs.items()},scope='Actual Prepared.new at candidate12 and parent equals the earlier emitted gamma_new method after its already recorded declaration-only new->gamma_new_new name transport. Select whole raw emitted body unchanged. Reuse identical current carriers/constants/folds, owner namespace/import changes only. New external boundary must bind scalar_k to actual checked source; other common operations stay universal with no success/canonicality proposition.')
p=here/'rho-prepared-source-layout.json';b=(json.dumps(meta,indent=2)+'\n').encode()
if a.check:assert p.read_bytes()==b
else:p.write_bytes(b)
print(json.dumps(dict(check=a.check,actual_prepared_source_identical=True,whole_generated_function_unchanged=True)))
