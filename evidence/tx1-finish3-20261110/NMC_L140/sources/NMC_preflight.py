"""Final own-workspace validation; no prover/native regression is launched."""
from pathlib import Path
import json,hashlib,shutil,sys
B=Path.cwd();S=B/'NMC_src'
def H(p):
 digest=hashlib.sha256()
 with p.open('rb')as f:
  for block in iter(lambda:f.read(1024*1024),b''):digest.update(block)
 return digest.hexdigest()
pins=json.loads((B/'NMC_SOURCE_PINS.json').read_text());errors=[name for name,sha in pins.items()if not(S/name).is_file()or H(S/name)!=sha]
assert not errors,errors
base=json.loads((B/'NMC_BASE_EXPECTED.json').read_text());baseline=[]
modules=['NMC_program','NMC_segments','NLU_program','NLI_program','NLI_factory','NLI_rounds','NLC_native','NLC_factory']
for name,sha in base.items():
 raw=(S/name).read_bytes();changed=True
 while changed:
  changed=False
  for module in modules:
   for visibility in ['pub','pub(crate)']:
    for suffix in [('\n#[cfg(kani)]\n'+visibility+' mod '+module+';\n').encode(),('\n#[cfg(kani)]\n#[path = "'+module+'.rs"]\n'+visibility+' mod '+module+';\n').encode()]:
     if raw.endswith(suffix):raw=raw[:-len(suffix)];changed=True
 if hashlib.sha256(raw).hexdigest()!=sha:baseline.append(name)
assert not baseline,baseline
assert H(S/'Cargo.lock')=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
assert H(S/'KMX_stubs.rs')=='ad8efb63d8ff791274c91eff9ccc5b9fb126f5a3ac7f27aa811ca11b8e25c138'
from NMC_patch_inputs import moduleText
assert H(B/'NMC_HARNESSES.patch')==(B/'NMC_HARNESSES.patch.sha256').read_text().strip()
assert H(B/'NMC_HARNESSES.patch')==json.loads((B/'NMC_PATCH_EXPORT.json').read_text())['patch_sha256']
inputs=json.loads((B/'NMC_PATCH_INPUT_PINS.json').read_text())
for module,row in inputs.items():assert moduleText(module)==(S/row['path']).read_text()
seeds=json.loads((B/'NMC_SEED_PINS.json').read_text())['files'];seed_errors=[]
for row in seeds:
 for key in ['source','destination']:
  p=Path(row[key])
  if not p.is_file()or H(p)!=row['sha256']:seed_errors.append(str(p))
assert not seed_errors,seed_errors
# Only dead solver files of this job are removed; all40 native scopes ended.
assert all((B/f'NMC_K{n:03}'/'receipt.json').exists()for n in range(1,41))
removed=[]
for pattern in ['external-sat*.cnf','smt2_dec_problem*']:
 for p in(B/'NMC_tmp').rglob(pattern):
  if p.is_file()and not p.is_symlink():
   removed.append(dict(path=str(p),bytes=p.stat().st_size,sha256=H(p)));p.unlink()
(B/'NMC_SOLVER_CLEANUP.json').write_text(json.dumps(dict(dead_native_scopes=40,removed=removed,directories_deleted=[]),indent=2)+'\n')
tools=[]
for p in [Path('/home/dombarker/.cargo/bin/cargo-kani'),Path('/home/dombarker/.kani/kani-0.67.0/bin/cbmc')]:
 if p.is_file():tools.append(dict(path=str(p),resolved=str(p.resolve()),bytes=p.stat().st_size,sha256=H(p)))
size=sum(p.stat().st_size for p in B.rglob('*')if p.is_file()and not p.is_symlink());assert size<30_000_000_000,size
free=shutil.disk_usage(B).free;assert free>=40_000_000_000,free
result=dict(status='PASS_FINAL_PREFLIGHT',frozen_source_files=len(base),selected_source_files=len(pins),seeded_files=len(seeds),source_errors=[],baseline_errors=[],seed_errors=[],lock_unchanged=True,copy_mitigation_exact=True,patch_inputs_exact=True,workspace_bytes=size,free_disk_bytes=free,tools=tools,cache_retained=True,TMPDIR_retained=True,target_retained=True,keys_or_wallets_touched=False)
(B/'NMC_PREFLIGHT.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items()if k not in ['tools']}))
