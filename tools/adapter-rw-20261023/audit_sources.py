#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,re,subprocess
R=Path(__file__).resolve().parents[2];E=R/'docs/research/100bit-spend-path-20261013/evidence/adapter-rw-20261023'
old=subprocess.check_output(['git','show','81521c77f7:programs/r1-cost-probe/src/r1_pool_adapter.rs'],cwd=R,text=True)
new=(R/'programs/r1-cost-probe/src/r1_pool_adapter.rs').read_text()
rows=[]
for match in re.finditer(r'(?m)^(?:pub\(super\) )?fn (\w+)\(',old):
 name=match[1];start=match.start();brace=old.index('{',match.end());depth=1;end=brace+1
 while depth:
  if old[end]=='{':depth+=1
  if old[end]=='}':depth-=1
  end+=1
 body=old[start:end]
 if name in ['stage1','stage2']:continue
 assert body in new,name
 rows.append({'function':name,'sha256':hashlib.sha256(body.encode()).hexdigest(),'body_identical':True})
assert (R/'programs/r1-cost-probe/src/r1_pool_adapter_original.rs').read_text()==old
base=json.loads((E/'candidate-sources.json').read_text())
changes=[]
for row in base['files']:
 p=R/row['path'];h=hashlib.sha256(p.read_bytes()).hexdigest()
 if h!=row['sha256']:changes.append({'path':row['path'],'built_sha256':row['sha256'],'current_sha256':h,'reason':'test-only canonical duplicate fixture correction after all three release builds'})
assert all(c['path']=='programs/r1-cost-probe/src/adapter_rw_tests.rs' for c in changes)
(E/'source-audit.json').write_text(json.dumps({'base_revision':'81521c77f7','original_fixture_byte_identical':True,'unchanged_adapter_children':rows,'caller_replacement':['stage1','stage2'],'new_ports':['OwnedAccount','snapshot','stage1_owned','stage2_owned','authenticate_asq8_accounts','authenticate_invariant_release_registry','validate_asq8'],'post_build_changes':changes,'transitive_inventory':'candidate-sources.json; every original file except lib.rs and r1_pool_adapter.rs matches prior S2E inventory; new owned/test files added','proved_cone_reuse':'body identity only; native/source/binary interpretations still require candidate joins'},indent=2)+'\n')
print(len(rows),'unchanged child/helper bodies')
