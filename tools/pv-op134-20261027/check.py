"""Compile-free generator and boundary preflight; receipt audit is separate."""
from pathlib import Path
import subprocess,sys,re,json
root=Path(__file__).resolve().parents[2]
for name in ['generate_order','generate_inventory','generate_rows','generate_row_spec','generate_row_order','generate_masks','generate_mask_spec']:
 subprocess.run([sys.executable,str(Path(__file__).with_name(name+'.py')),'--check'],check=True)
lean=root/'docs/research/v8-r0-zk-20261009/lean/R1Z'
for p in lean.glob('PV_Op134_*.lean'):
 s=p.read_text()
 assert not re.search(r'\b(sorry|admit|native_decide|implemented_by|axiom)\b',s),p
 assert not re.search(r'set_option\s+(maxHeartbeats|maxRecDepth)',s),p
 for theorem in re.findall(r'^theorem (\w+)',s,re.M):
  assert '#print axioms '+theorem in s,(p,theorem)
# Every old published statement AND proof remains byte-stable.
for p in lean.glob('PV_CBM_*.lean'):
 old=subprocess.check_output(['git','show','8483406290:'+str(p.relative_to(root))],cwd=root)
 assert old==p.read_bytes(),p
print('PASS: generators, theorem audit commands, forbidden constructs, stable PV_CBM bundle')
