from pathlib import Path
import json,subprocess,difflib,hashlib,tempfile
E=Path(__file__).resolve().parent
old=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:crates/aspis-r1-cost-probe/src/lib.rs'],text=True);rows=[]
for payload,patch in [('NHH_NATIVE_INPUTS.json','NHH_harness_base.patch'),('NHH_ARG_CM_INPUTS.json','NHH_harness_cm.patch'),('NHH_ARG_Q_INPUTS.json','NHH_harness.patch'),('NHH_CM_ZERO_INPUTS.json','NHH_harness_cm_zero.patch')]:
 x=json.loads((E/payload).read_text());n='crates/aspis-r1-cost-probe/src/lib.rs';out=''.join(difflib.unified_diff(old.splitlines(True),x[n].splitlines(True),fromfile='a/'+n,tofile='b/'+n));h='crates/aspis-r1-cost-probe/src/NHH_fields.rs';out+=''.join(difflib.unified_diff([],x[h].splitlines(True),fromfile='/dev/null',tofile='b/'+h));(E/patch).write_text(out)
 with tempfile.TemporaryDirectory(prefix='NHH_patch_')as td:
  root=Path(td);p=root/n;p.parent.mkdir(parents=True);p.write_text(old)
  subprocess.run(['git','apply','--check',str((E/patch).resolve())],cwd=root,check=True,capture_output=True)
  subprocess.run(['git','apply',str((E/patch).resolve())],cwd=root,check=True,capture_output=True)
  assert (root/n).read_text()==x[n]and(root/h).read_text()==x[h]
 rows.append(dict(payload=payload,patch=patch,sha256=hashlib.sha256(out.encode()).hexdigest(),applies_to_frozen=True,reconstructs_exact_payload=True))
(E/'NHH_PATCHES.json').write_text(json.dumps(dict(status='PASS',frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',patches=rows,required_copy_patch='evidence/kani-mitig-20261028/KMX_copy_stubs.patch',copy_patch_sha256='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67',shipped_files_modified=False),indent=1)+'\n')
print('PASS four exact scratch-source patches')
