#!/usr/bin/env python3
"""Build a source-only focused-extractor-proof-packet-v1 manifest."""
from pathlib import Path
import hashlib,json
R=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
# Map direct Lean import names to the exact included source snapshot used for review.
source_for={
 'Aeneas':'sources/dependencies/Aeneas.lean',
 'Aeneas.Std.RangeIter':'sources/dependencies/Aeneas/Std/RangeIter.lean',
 'AspisR1GroupedPairActualFieldOpsV3.Funs':'sources/actual/Funs.lean',
 'CurrentFinishField':'sources/dependencies/CurrentFinishField.lean',
 'CurrentWideLinearExact':'sources/dependencies/CurrentWideLinearExact.lean',
 'S3ActualFieldOpsComplete':'sources/proofs/S3ActualFieldOpsComplete.lean',
 'S3ActualGeneratedLoop0Body':'sources/proofs/S3ActualGeneratedLoop0Body.lean',
 'AspisR1GroupedPairCut.Proofs.S3GroupedPairArrayMeaning':'sources/dependencies/S3GroupedPairArrayMeaning.lean',
}
module_names={
 'actual-generated-loop0-body-v10':'S3ActualGeneratedLoop0Body',
 'actual-field-ops-complete-v1':'S3ActualFieldOpsComplete',
 'actual-loop0-complete-operations-v1':'S3ActualLoop0WithCompleteOperations',
 'actual-group-table-bound-v1':'S3ActualGroupTableBound',
 'actual-group-table-transfer-v2':'S3ActualGroupTableTransfer',
}
modules=[]; global_imports={}
for attempt,module in module_names.items():
 d=R/'attempts'/attempt/'proof-evidence'
 pre=json.loads((d/'preflight.json').read_text()); rec=json.loads((d/'receipt.json').read_text()); cmd=json.loads((d/'command.json').read_text())
 imports={}
 for name,owner in pre['direct_imports'].items():
  if isinstance(owner,dict): obj=owner['sha256']; objpath=owner['path']
  else: obj=owner; objpath=None
  src=source_for.get(name)
  entry={'object_sha256':obj,'compiled_object_path':objpath,'source_path':src,'source_sha256':sha(R/src) if src and (R/src).is_file() else None,'source_correspondence':'included exact source snapshot; imported object pin is the recorded preflight hash'}
  imports[name]=entry
  global_imports[name]=entry
 source_rel=pre['source'].split('/sources/',1)[-1]
 # Worker source is carried in our canonical source subdirectories, not under the remote 'sources' root.
 matching=[x for x in (R/'sources').rglob('*.lean') if sha(x)==pre['source_sha256']]
 if len(matching)!=1: raise RuntimeError(f'{module}: source hash matches {len(matching)} included files')
 source=matching[0].relative_to(R).as_posix()
 axioms=[]
 log=(d/'lean.log').read_text()
 import re
 matches=re.findall(r'depends on axioms:\s*\[(.*?)\]',log,re.S)
 if matches:
  axioms=sorted({x.strip() for match in matches for x in match.split(',') if x.strip()})
 modules.append({'module':module,'source_path':source,'source_sha256':sha(R/source),'object_sha256':rec['object_sha256'],'object_path_native_cache':pre['object'],'source_revision':pre['source_revision'],'attempt_dir':f'attempts/{attempt}','command_path':f'attempts/{attempt}/proof-evidence/command.json','preflight_path':f'attempts/{attempt}/proof-evidence/preflight.json','receipt_path':f'attempts/{attempt}/proof-evidence/receipt.json','lean_log_path':f'attempts/{attempt}/proof-evidence/lean.log','time_log_path':f'attempts/{attempt}/proof-evidence/time.log','exit_status':rec['exit_status'],'wall_seconds':rec['wall_seconds'],'peak_rss_kib':rec.get('peak_process_rss_kib'),'scope_peak_bytes':rec.get('scope_memory_peak_bytes'),'swap_peak_bytes':rec.get('scope_swap_peak_bytes'),'axioms':axioms,'direct_imports':imports,'toolchain':pre['lean'],'toolchain_sha256':pre['lean_sha256'],'resource_caps':pre['limits']})
# Repository-standard manifest entry point; it summarizes the focused modules
# and pins each source, receipt, object, compiler, resource cap, axioms, and imports.
standard_modules=[]
for m in modules:
 standard_modules.append({
  'module':m['module'],'source':m['source_path'],'source_sha256':m['source_sha256'],
  'object_sha256':m['object_sha256'],'object_path_native_cache':m['object_path_native_cache'],
  'receipt':m['receipt_path'],'receipt_sha256':sha(R/m['receipt_path']),
  'preflight':m['preflight_path'],'command':m['command_path'],
  'lean_log':m['lean_log_path'],'time_log':m['time_log_path'],
  'exit_status':m['exit_status'],'wall_seconds':m['wall_seconds'],
  'peak_rss_kib':m['peak_rss_kib'],'scope_peak_bytes':m['scope_peak_bytes'],
  'swap_peak_bytes':m['swap_peak_bytes'],'source_revision':m['source_revision'],
  'compiler':m['toolchain'],'compiler_sha256':m['toolchain_sha256'],
  'resource_caps':json.loads((R/m['preflight_path']).read_text())['limits'],
  'axioms':m['axioms'],'direct_imports':m['direct_imports']})
standard_files={}
for p in sorted(R.rglob('*')):
 if not p.is_file() or p.name in ('manifest.json','packet.json'): continue
 rel=p.relative_to(R).as_posix()
 if p.suffix in ('.olean','.ir','.exe','.rlib','.a','.so','.dylib','.tar','.gz'):
  raise RuntimeError(f'forbidden binary/artifact in source-only packet: {rel}')
 standard_files[rel]=sha(p)
owner_producers=[]
for phase,module,source in [
 ('types','AspisR1GroupedPairActualFieldOpsV3.Types','sources/actual/Types.lean'),
 ('funs','AspisR1GroupedPairActualFieldOpsV3.Funs','sources/actual/Funs.lean')]:
 base=f'attempts/actual-field-ops-v3/{phase}-evidence/'
 pre=json.loads((R/(base+'preflight.json')).read_text())
 rec=json.loads((R/(base+'receipt.json')).read_text())
 owner_producers.append({
  'module':module,'source':source,'source_sha256':sha(R/source),
  'object_sha256':rec['object_sha256'],'object_path_native_cache':pre['object'],
  'receipt':base+'receipt.json','receipt_sha256':sha(R/(base+'receipt.json')),
  'preflight':base+'preflight.json','command':base+'command.json',
  'lean_log':base+'lean.log','time_log':base+'time.log',
  'source_revision':pre['source_revision'],'exit_status':rec['exit_status'],
  'wall_seconds':rec['wall_seconds'],'peak_rss_kib':rec['peak_process_rss_kib'],
  'scope_peak_bytes':rec['scope_memory_peak_bytes'],'swap_peak_bytes':rec['scope_swap_peak_bytes'],
  'compiler':pre['lean'],'compiler_sha256':pre['lean_sha256'],
  'resource_caps':pre['limits'],'direct_imports':pre['direct_imports']})
standard={
 'schema':'focused-extractor-proof-packet-v1','packet_id':'s3-actual-grouped-loop0-step-v1-20261020',
 'status':'source-cut and focused Lean proof evidence; no production adoption or whole-helper claim',
 'source_revision':'8137980396719c48f71f743254644aaf0a3a8423',
 'source_cut_checker':'check_source_cut.py','source_cut_checker_sha256':sha(R/'check_source_cut.py'),
 'corrected_source_pins':'corrected-source-pins.json','provenance_correction':'provenance-correction.json',
 'direct_import_source_map':global_imports,'modules':standard_modules,
 'owner_producers':owner_producers,
 'extraction':{
  'charon_receipt':'attempts/actual-cut-v5/charon-a/receipt.json','aeneas_receipt':'attempts/actual-cut-v5/aeneas-a/receipt.json',
  'llbc':'sources/extraction-v5/S3GroupedPair.llbc','llbc_sha256':sha(R/'sources/extraction-v5/S3GroupedPair.llbc'),
  'generated_funs':'sources/extraction-v5/generated/AspisR1GroupedPairActualCut/Funs.lean','generated_funs_sha256':sha(R/'sources/extraction-v5/generated/AspisR1GroupedPairActualCut/Funs.lean'),
  'generated_types':'sources/extraction-v5/generated/AspisR1GroupedPairActualCut/Types.lean','generated_types_sha256':sha(R/'sources/extraction-v5/generated/AspisR1GroupedPairActualCut/Types.lean'),
  'adapted_funs':'sources/actual/Funs.lean','adapted_funs_sha256':sha(R/'sources/actual/Funs.lean'),
  'adapted_types':'sources/actual/Types.lean','adapted_types_sha256':sha(R/'sources/actual/Types.lean'),
  'sidecar_status':'original receipt binds stale source-pins.json; correction is separate and tested'},
 'unresolved':['whole 64-iteration helper prefix is not proved','success of decoding all input bytes is not derived','loop 1 and full-helper return are not proved','production adoption and runtime claims are outside this packet'],
 'files':standard_files}
(R/'manifest.json').write_text(json.dumps(standard,indent=2,sort_keys=True)+'\n')
# Files list covers every packet file other than packet.json; manifest is itself pinned there.
files={}
for p in sorted(R.rglob('*')):
 if not p.is_file() or p.name=='packet.json': continue
 rel=p.relative_to(R).as_posix()
 if p.suffix in ('.olean','.ir','.exe','.rlib','.a','.so','.dylib','.tar','.gz'):
  raise RuntimeError(f'forbidden binary/artifact in source-only packet: {rel}')
 files[rel]=sha(p)
manifest={
 'schema':'focused-extractor-proof-packet-v1',
 'packet_id':'s3-actual-grouped-loop0-step-v1-20261020',
 'classification':'focused source-cut and Lean proof evidence; candidate/proof frontier only, not production adoption',
 'source_revision':'8137980396719c48f71f743254644aaf0a3a8423',
 'source_cut_checker':'check_source_cut.py',
 'source_cut_checker_sha256':sha(R/'check_source_cut.py'),
 'corrected_source_pin':'corrected-source-pins.json',
 'provenance_correction':'provenance-correction.json',
 'direct_import_source_map':global_imports,
 'proof_modules':modules,
 'extraction':{
  'actual_kit':'sources/extraction-v5/input',
  'actual_source_snapshot':'sources/rust-upstream',
  'llbc':'sources/extraction-v5/S3GroupedPair.llbc',
  'llbc_sha256':sha(R/'sources/extraction-v5/S3GroupedPair.llbc'),
  'translation':'sources/extraction-v5/generated/AspisR1GroupedPairActualCut/translation.json',
  'translation_sha256':sha(R/'sources/extraction-v5/generated/translation.json'),
  'generated_types':'sources/extraction-v5/generated/AspisR1GroupedPairActualCut/Types.lean',
  'generated_types_sha256':sha(R/'sources/extraction-v5/generated/AspisR1GroupedPairActualCut/Types.lean'),
  'generated_funs':'sources/extraction-v5/generated/AspisR1GroupedPairActualCut/Funs.lean',
  'generated_funs_sha256':sha(R/'sources/extraction-v5/generated/AspisR1GroupedPairActualCut/Funs.lean'),
  'adapted_types':'sources/actual/Types.lean','adapted_types_sha256':sha(R/'sources/actual/Types.lean'),
  'adapted_funs':'sources/actual/Funs.lean','adapted_funs_sha256':sha(R/'sources/actual/Funs.lean'),
  'charon_receipt':'attempts/actual-cut-v5/charon-a/receipt.json',
  'aeneas_receipt':'attempts/actual-cut-v5/aeneas-a/receipt.json',
  'original_source_pins_sha256':'658f1e663d1b327add266e4c56ae7927dbc78ad3f32b50a1e7c9ec0ad258c320',
  'source_pin_status':'original receipt sidecar is stale; corrected pin/checker supplied, and defect remains visible'
 },
 'proved_scope':['generated loop0 body succeeds under explicit next/index/decode/add/update success premises','actual decodeField success yields canonical actual WideExact values','actual add operation is total/exact over canonical values','actual generated loop0 body instantiates with concrete parser/add operations','actual S2 group table index values are <12 via exact equality to accepted prior table'],
 'unresolved_scope':['whole s2_grouped_inactive_pair loop and return are not yet proved','decodeField success from arbitrary input bytes is not derived here','loop 1/weight/mul path is not covered','source shim is a minimal cut, not full Rust crate extraction','production adoption and runtime claims are not made'],
 'files':files
}
(R/'packet.json').write_text(json.dumps(manifest,indent=2,sort_keys=True)+'\n')
print(f'Wrote packet.json with {len(files)} file hashes, {len(modules)} proof modules, {len(global_imports)} imported owners')
