"""Source-fission of the exact six-call frozen addition chain, with erasure pin.
Only the arithmetic callee expressions are replaced by local-record oracles.
"""
from pathlib import Path
import subprocess,hashlib,json
E=Path(__file__).resolve().parent;R=E.parents[1]
rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';path='crates/aspis-core/src/state_only_hiding.rs'
src=subprocess.check_output(['git','show',rev+':'+path],cwd=R).decode()
body=src.split('fn mask_power_26(value: QM31) -> QM31 {',1)[1].split('\n}',1)[0]
changes=[('value.square()','square_cut(value, log)'),('x2.square()','square_cut(x2, log)'),('x4.square()','square_cut(x4, log)'),('x8.square()','square_cut(x8, log)'),('x16.mul(x8).mul(x2)','{ let x24 = multiply_cut(x16,x8,log); multiply_cut(x24,x2,log) }')]
cut=body
for before,after in changes:assert cut.count(before)==1;cut=cut.replace(before,after)
erased=cut
for before,after in reversed(changes):assert erased.count(after)==1;erased=erased.replace(after,before)
assert erased==body
(E/'NHU_power_body.rs.txt').write_text('fn NHU_power26_cut(value:QM31,log:&mut PowerLog)->QM31{'+cut+'\n}\n')
(E/'NHU_POWER_ERASURE.json').write_text(json.dumps(dict(status='PASS',revision=rev,source_path=path,source_sha256=hashlib.sha256(src.encode()).hexdigest(),body_sha256=hashlib.sha256(body.encode()).hexdigest(),erased_sha256=hashlib.sha256(erased.encode()).hexdigest(),replacements=changes,copy='No caller code or arithmetic result assertion is inserted into the source cut; domain assertions/log updates belong only to callees'),indent=1)+'\n')
