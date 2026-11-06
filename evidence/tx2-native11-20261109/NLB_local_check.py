"""Local source/evidence hygiene; no formal process or remote mutation."""
from pathlib import Path
import subprocess,json,hashlib,lzma,shutil
E=Path(__file__).resolve().parent
repo=E.parents[1]
rel=E.relative_to(repo)
base=json.loads((E/'NLB_TARGET.json').read_text())['base_revision']
for p in E.rglob('__pycache__'):
 if p.is_dir():shutil.rmtree(p)
branch=subprocess.check_output(['git','branch','--show-current'],text=True,cwd=repo).strip()
assert branch=='codex/cx-tx2-native11-20261107'
paths=set(subprocess.check_output(['git','diff','--name-only',base,'HEAD','--'],text=True,cwd=repo).splitlines())|set(subprocess.check_output(['git','ls-files','--others','--exclude-standard'],text=True,cwd=repo).splitlines())
assert all(p.startswith(str(rel)+'/') for p in paths)
raw=subprocess.run(['git','diff','--check',base,'HEAD','--',str(rel)],capture_output=True,cwd=repo);data=raw.stdout+raw.stderr
(E/'NLB_RAW_DIFF_CHECK.log.xz').write_bytes(lzma.compress(data));(E/'NLB_RAW_DIFF_CHECK.log.sha256').write_text(hashlib.sha256(data).hexdigest()+'\n')
curated=[str(p.relative_to(repo)) for p in E.iterdir() if p.is_file() and p.suffix in ['.lean','.py','.md','.json']]
check=subprocess.run(['git','diff','--check',base,'HEAD','--',*curated],capture_output=True,cwd=repo)
assert check.returncode==0,check.stdout.decode()
large=[str(p.relative_to(repo)) for p in E.rglob('*') if p.is_file() and p.stat().st_size>20_000_000];assert not large,large
for module,attempt in [('NLB_Driver','NLB_L063'),('NLB_ProofDriver','NLB_L051')]:
 assert (E/(module+'.lean')).read_bytes()==(E/attempt/'sources/NLB_generated'/(module+'.lean')).read_bytes()
assert not (E/'NLB_CLIENT_ACTIVE').exists() and not (E/'NLB_HOLD').exists()
x=dict(branch=branch,base_revision=base,scope_only=True,changed_paths=len(paths),curated_source_diff_check_exit=check.returncode,raw_evidence_diff_check_exit=raw.returncode,raw_evidence_note='Verbatim logs and inherited generated C retain trailing whitespace/blank EOF. Do not normalize pinned evidence. Initial broad local QA stopped here; reporting corrected to distinguish curated sources from evidence.',raw_diff_receipt='NLB_RAW_DIFF_CHECK.log.xz',over20MB=large,driver_sources_match_passing_compiles=True,pycache_removed=True,own_active_client=False,no_push=True)
(E/'NLB_LOCAL_CHECK.json').write_text(json.dumps(x,indent=2)+'\n')
print(json.dumps(dict(scope_only=True,source_diff_check_exit=0,raw_evidence_diff_check_exit=raw.returncode,over20MB=0)))
