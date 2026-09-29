#!/usr/bin/env python3
import argparse, json, shutil
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True);a=p.parse_args()
assert not a.output.exists();a.output.mkdir(parents=True)
root=Path('/home/dombarker/project-offloads');out=a.output
def copy(src,dst):
    assert src.is_file() and 'keypair' not in str(src)
    dst.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src,dst)
final=root/'aspis-r63-lean-20260929-b'
for name in ['InverseFieldSlice.log','InverseRuntimeMul.log','GeneratedInverseLoop.log','metadata.json','dependency-pins.json']:
    copy(final/name,out/'lean'/name)
copy(final/'source-audit.json',out/'source/audit.json')
stage=root/'aspis-v7-aeneas-source-unblock-20260830/staged-current-normalized-statement-owned-twohelpers-r19/V7Tag73CurrentHelpersOpaque'
for name in ['Types.lean','FunsChunk04.lean']:copy(stage/name,out/'source/generated'/name)
selected=root/'aspis-r20-r62-gather-20260929-b'
copy(selected/'r18-stage.json',out/'source/r18-stage.json')
copy(selected/'crates/aspis-core/src/field.rs',out/'source/selected-field.rs')
pre=root/'aspis-r63-runtime-20260929-a'
for path in sorted(pre.glob('GeneratedInverseLoop.previous-*.log')):copy(path,out/'development'/path.name)
copy(pre/'InverseRuntimeProbe.log',out/'development/InverseRuntimeProbe.log')
(out/'development/notes.json').write_text(json.dumps({
 'early_probe_failures':['cache package-root shadowing','unknown val_inj name'],
 'slice_import_fix':['Scalar.Casts','Tactic.RustAttributes'],
 'loop_fixes':['explicit multiplication bound type','parenthesized field term','strict max bound after simp','preserve recursive body under lambda','reduce pair match before rewrite'],
 'first_release_preflight':'stopped before compilation because selected R62 M31.mul is guarded one-fold, unlike retained extraction',
 'resolution':'record exact selected body and leave optimized execution bridge open; generated-source pins unchanged',
 'no_memory_kill':True,'no_cap_increase':True},indent=2)+'\n')
print(json.dumps({'output':str(out),'files':sum(p.is_file() for p in out.rglob('*'))}))
