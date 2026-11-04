"""Inventory E001's text-only template and every canonical interpretation."""
from pathlib import Path
import re,json,hashlib,subprocess
E=Path(__file__).resolve().parent; O=E.parent/'pool-retdata-20261104'
p=O/'NFO_E001_outputs/NFO_decode_extracted__NFO_DecodeExtracted__FunsExternal_Template.lean.txt'
names=re.findall(r'(?m)^axiom\s+([\w.]+)',p.read_text())
assert len(names)==19
rows=[]
constants={
'POOL_V1_DIGEST_ENCODING_VERSION':('NFR_ExtractedDecode.digestVersion','ok 1','crates/aspis-statement/src/pool_v1/format.rs'),
'POOL_V1_PAIR_FOREST_TERMINAL_RESULT_MAGIC':('NFR_ExtractedDecode.resultMagic','ok ASR8','crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs'),
'POOL_V1_PAIR_FOREST_TERMINAL_VERSION':('NFR_ExtractedDecode.resultVersion','ok 1','crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs'),
'POOL_V1_PAIR_FOREST_TERMINAL_RESULT_BYTES':('NFR_ExtractedDecode.resultBytes','ok (8+3*32+(8+680)) = ok 792','crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs'),
'RESULT_MASTER_OFFSET':('NFR_ExtractedDecode.masterOffset','ok 8','crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs'),
'RESULT_SELECTED_LANE_OFFSET':('NFR_ExtractedDecode.selectedOffset','ok 40','crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs'),
'RESULT_NULLIFIER_OFFSET':('NFR_ExtractedDecode.nullifierOffset','ok 72','crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs'),
'RESULT_AFTERSTATE_OFFSET':('NFR_ExtractedDecode.afterstateOffset','ok 104','crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs'),
'POOL_V1_PAIR_TREE_STORAGE_FORMAT_VERSION':('AspisR1TerminalDecoder.pool_v1.pair_tree_profile.POOL_V1_PAIR_TREE_STORAGE_FORMAT_VERSION','1; within canonical child decoder','crates/aspis-statement/src/pool_v1/pair_tree_profile.rs'),
'POOL_V1_PAIR_VERIFIED_AFTERSTATE_MAGIC':('AspisR1TerminalDecoder.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_MAGIC','ASJA; within canonical child decoder','crates/aspis-statement/src/pool_v1/pair_terminal.rs'),
'POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES':('AspisR1TerminalDecoder.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES','ok (8+680)=ok 688; within canonical child decoder','crates/aspis-statement/src/pool_v1/pair_terminal.rs'),
'POOL_V1_PAIR_VERIFIER_TRANSPORT_VERSION':('AspisR1TerminalDecoder.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIER_TRANSPORT_VERSION','1; within canonical child decoder','crates/aspis-statement/src/pool_v1/pair_terminal.rs')}
for n in names:
 key=n.split('.')[-1]
 if key in constants:
  owner,value,path=constants[key]
  row=dict(external=n,kind='frozen constant',interpretation=owner,value=value,source=path,association='NFR_ExtractedDecode.probe for reached top slots; inherited canonical child definitions for transitive slots')
 elif n=='Slice.Insts.CoreCmpPartialEqArray.ne':
  row=dict(external=n,kind='stdlib comparison',interpretation='NFR_ExtractedDecode.sliceArrayNe',
   association='NFR_ExtractedDecode.sliceArrayNe_eq; canonical slice comparison after Array.to_slice; existing Std interpretation retained; NFO_K054 source cut')
 elif n=='core.result.Result.map_err':
  row=dict(external=n,kind='stdlib Result map',interpretation='AspisR1TerminalDecoder.core.result.Result.map_err',
   association='NFO_DecodeErrors.{master,selected,digest_width,digest,afterstate}; NFR_RawInverseHelpers map provenance; identical closure return bodies')
 elif key=='from_le_bytes':
  row=dict(external=n,kind='field child',interpretation='AspisR1TerminalDecoder.aspis_core.field.M31.from_le_bytes',
   association='CLOSED digest child NEQ; emitted canonical definition; NFO_M31Roundtrip.canonical_word; no multiplication')
 elif key=='pool_v1_pair_forest_output_lane_v1':
  row=dict(external=n,kind='validator child',interpretation='AspisR1TerminalDecoder.pool_v1.pair_forest_accounts.pool_v1_pair_forest_output_lane_v1',
   association='CLOSED validate_result child NEQ/NBX; NFO_K054 full validator argument and Result association')
 elif key=='encode_pool_v1_pair_verified_afterstate_v1':
  row=dict(external=n,kind='afterstate encoder child',interpretation='AspisR1TerminalDecoder.pool_v1.pair_terminal.encode_pool_v1_pair_verified_afterstate_v1',
   association='CLOSED child NEX; AspisS6NativeAfterstateCodec.encode_total and accepted_inverse')
 elif key=='exact':
  row=dict(external=n,kind='slice child',interpretation='AspisR1TerminalDecoder.pool_v1.pair_terminal.exact',
   association='inherited canonical exact definition; AspisS6NativeAfterstateDecodeHelpers.exact_spec; NBH_Exact source/accepted_bytes')
 elif key=='validate_verified_afterstate':
  row=dict(external=n,kind='afterstate validation child',interpretation='AspisR1TerminalDecoder.pool_v1.pair_terminal.validate_verified_afterstate',
   association='CLOSED afterstate decoder NEX; AspisS6NativeAfterstateCodec.accepted_frames')
 else: raise AssertionError(n)
 rows.append(row)
pins=[]
for path in sorted(set(x['source'] for x in rows if 'source' in x)):
 b=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+path])
 pins.append(dict(path=path,revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',sha256=hashlib.sha256(b).hexdigest(),size=len(b)))
out=dict(template_path=str(p.relative_to(E.parent.parent)),template_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),
 template_axioms=19,imported_template_axioms=0,rows=rows,frozen_source_pins=pins,
 scope='Canonical-owner interpretation of selected emitted decoder body and its CLOSED children. External template remains text, never imported. No claim of a runtime syscall implementation or removal of existing P6/Std/extraction trust.')
(E/'NFR_B_TEMPLATE_AUDIT.json').write_text(json.dumps(out,indent=1)+'\n')
print('Mapped all',len(rows),'E001 template declarations; template imports zero')
