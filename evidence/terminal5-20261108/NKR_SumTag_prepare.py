"""The218 tag-registry metadata/permutation cut reads only frozen constants."""
from pathlib import Path
import subprocess,json,difflib,hashlib
E=Path(__file__).resolve().parent
rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
source='crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs'
old=subprocess.check_output(['git','show',rev+':'+source],text=True)
code=(E/'NKR_SumTag_native.rs.txt').read_text()
name='crates/aspis-statement/src/pool_v1/NKR_SumTag_native.rs'
new=old+'\n#[cfg(kani)]\n#[path="NKR_SumTag_native.rs"]\nmod NKR_tag_native;\n'
patch=''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+source,tofile='b/'+source))
patch+=''.join(difflib.unified_diff([],code.splitlines(True),fromfile='/dev/null',tofile='b/'+name))
(E/'NKR_SumTag_native.patch').write_text(patch)
(E/'NKR_SumTag_PINS.json').write_text(json.dumps(dict(revision=rev,source=source,source_sha256=hashlib.sha256(old.encode()).hexdigest(),harness_sha256=hashlib.sha256(code.encode()).hexdigest(),assertions='metadata:tag in1124073472+[0,136),actual136link tag/block match,actualgc=coordinate inside actualoffset interval;permutation:tag+side map injective on272positions',consumer='NKR218 cohort tag sum regrouping;no independent rowcredit'),indent=2))
