from pathlib import Path
import json,subprocess,sys,hashlib,re
from NCD_expected import expected
E=Path(__file__).resolve().parent;tag,start,crate,patchfile,*harnesses=sys.argv[1:];start=int(start);patch=Path(patchfile);validation=expected(patch);template=json.loads((E/'NCD_K006.json').read_text());rows=[]
frozen=json.loads((E.parent/'native-tx2h-20261028/NBQ_SCRATCH_MANIFEST.json').read_text());modified=sorted(n for n,h in validation['after'].items() if frozen.get(n)!=h)
negative='r0::heap::NCB_allocation::copy_negative' if crate=='aspis-core' else 'verifier::NCB_prefix::copy_negative'
for i,h in enumerate([negative]+harnesses,start):
 a=f'NCD_K{i:03d}';assert not (E/(a+'.json')).exists();c=json.loads(json.dumps(template));c.update(attempt=a,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=True,reservation_retries=0,expected_time='optimized native '+h)
 c['sources']=['NCD_src/'+n for n in ['Cargo.toml','Cargo.lock']+modified];j=c['command'].index('--harness')+1;c['command'][j]=h;j=c['command'].index('--manifest-path')+1;c['command'][j]='/home/dombarker/project-offloads/codex-cx-native-tx2m-20261028/NCD_src/crates/'+crate+'/Cargo.toml'
 c['deps_fingerprint'].update(kmx_patch_sha256=validation['kmx_patch_sha256'],harness_patch_sha256=hashlib.sha256(patch.read_bytes()).hexdigest(),cfg_patch_chain=validation['patch_chain'],scratch_source_manifest_sha256=hashlib.sha256(json.dumps(validation['after'],sort_keys=True).encode()).hexdigest(),matching_copy_negative_control=f'NCD_K{start:03d}')
 rows.append(dict(cfg=c,expected_negative=i==start))
slots=sum(bool(re.fullmatch(r'NCD_K[0-9]+\.json',p.name)) for p in E.iterdir());assert slots+len(rows)<=50,(slots,len(rows))
plan=dict(scratch='/home/dombarker/project-offloads/codex-cx-native-tx2m-20261028/NCD_src',rows=rows,source_manifest=validation['after'],source_check=validation,patch=patch.read_text(),runner=(E/'NCD_native_batch_host.py').read_text())
(E/('NCD_native_'+tag+'_plan.json')).write_text(json.dumps(plan,indent=2)+'\n');(E/(f'NCD_K{start:03d}-harness.patch')).write_bytes(patch.read_bytes());print(len(rows), 'native targets')
