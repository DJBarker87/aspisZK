#!/usr/bin/env python3
"""Read/hash accepted pinned static translator and its exact source patch."""
from pathlib import Path
import hashlib,json,subprocess
W=Path('/home/dombarker/project-offloads/aspis-r1-public-binding-followup-20261016')
P=Path('/home/dombarker/project-offloads/v7-tag73-challenge-qm31-source-20260825-work')
R=P/'toolchain/aeneas-full';B=P/'toolchain/output/aeneas-b59d5188-lean432-extended-static'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
expected='4632746db1bf6c3953f2971078965a2a5a8ad6cf5f75636b46b397bc50c550b5'
assert sha(B)==expected
patch=W/'tools/aeneas-b59d5188-lean432.patch';manifest=W/'tools/patched-aeneas-hashes.sha256';build=W/'tools/build-patched-aeneas.sh'
assert sha(patch)=='5abaafc2d345511dda0eb96cd40154daff137f79dc4bcfa8247a45acea639c9c'
assert sha(manifest)=='142e88198375125dd5e09fe8a21bc99deab8c6b16e998c3ad388cfab4a49bc3d'
assert expected in build.read_text() and '5a843e70672e4139232b2fdcb52a0c1fbd4b1619' in build.read_text()
assert subprocess.check_output(['git','-C',str(R),'rev-parse','HEAD'],text=True).strip()=='b59d5188c082f704a418c7cb4e52ad69328002d1'
files={}
for line in manifest.read_text().splitlines():
 h,n=line.split(None,1);assert sha(R/n)==h,n;files[n]=h
changed=subprocess.check_output(['git','-C',str(R),'diff','--name-only','HEAD'],text=True).splitlines()
assert set(changed)==set(files)|{'backends/lean/lake-manifest.json'},(changed,set(files))
assert sha(R/'backends/lean/lake-manifest.json')=='5d15524cf34ff705bebbd037e80baec63683d5d5a3a37a539a62f17405a2fc62'
version=subprocess.check_output([str(B),'-version'],text=True).strip();assert version=='aeneas b59d5188-lean432-extended'
result={'binary':str(B),'binary_sha256':expected,'version':version,'source_root':str(R),'base_revision':'b59d5188c082f704a418c7cb4e52ad69328002d1','patch_sha256':sha(patch),'post_patch_manifest_sha256':sha(manifest),'build_recipe_sha256':sha(build),'build_recipe_expected_tree':'5a843e70672e4139232b2fdcb52a0c1fbd4b1619','exact_changed_files':files,'additional_backend_lock_sha256':sha(R/'backends/lean/lake-manifest.json'),'scope':'Existing accepted static binary; no tool rebuild or patch. Exact38file source match and tracked recipe pins binary. Observer is safe nonvariadic Rust fn(Phase), effectful Result translation. R27 variant rejected for use because InterpExpansion differs.'}
(W/'extended-tool-audit.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
print(json.dumps({'binary_sha256':expected,'source_files_matched':len(files),'version':version}))
