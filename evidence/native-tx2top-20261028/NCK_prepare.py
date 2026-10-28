from pathlib import Path
import subprocess,json,hashlib,difflib
E=Path(__file__).resolve().parent
assert not (E/'NCK_kani.py').exists(),'setup is already materialized; never overwrite a repaired own runner'
rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
roots=['Cargo.toml','Cargo.lock','crates','programs','xtask','audit/poseidon-pair-probe/program','docs/research/v8-r0-zk-20261009/refine','docs/research/v8-r0-zk-20261009/z4','docs/research/v8-r0-zk-20261009/c3','tools/r1-builder-reference']
paths=subprocess.check_output(['git','ls-tree','-r','--name-only',rev,*roots],text=True).splitlines()
manifest={n:hashlib.sha256(subprocess.check_output(['git','show',rev+':'+n])).hexdigest() for n in paths}
(E/'NCK_FROZEN_MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
O=E.parent/'native-tx2l-20261028'
s=(O/'NCB_kani.py').read_text().replace('NCB_','NCK_').replace('native-tx2l','native-tx2top').replace('<70','<50')
s=s.replace("if not s.exists():s.symlink_to('/home/dombarker/project-offloads/codex-cx-native-tx2i-20261028/NBS_src',target_is_directory=True)","assert s.is_dir() and not s.is_symlink(),'own frozen scratch required'")
s=s.replace("json.loads((E.parent/'native-tx2h-20261028/NBQ_SCRATCH_MANIFEST.json').read_text())","json.loads((E/'NCK_FROZEN_MANIFEST.json').read_text())")
s=s.replace("patch=request.read_text();validated=expected(request)","validated=expected(request);patch=validated['combined_patch']")
(E/'NCK_kani.py').write_text(s)
