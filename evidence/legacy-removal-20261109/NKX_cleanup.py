"""Remove only this job's rebuildable Cargo target; keep sources/artifacts/receipts."""
from pathlib import Path
import json,shutil,subprocess,time,resource
B=Path('/home/dombarker/project-offloads/codex-cx-legacy-removal-20261109')
t=time.monotonic();target=B/'target'
assert not target.is_symlink() and target.resolve().parent==B
keys=[str(p) for p in B.rglob('*keypair*.json') if p.is_file()]
assert not keys,('Keep all outputs: unexpected key file',keys)
before=int(subprocess.check_output(['du','-sb',str(B)],text=True).split()[0]);assert before<20_000_000_000
shutil.rmtree(target)
after=int(subprocess.check_output(['du','-sb',str(B)],text=True).split()[0])
r=resource.getrusage(resource.RUSAGE_SELF)
x=dict(kind='OWN_BUILD_OUTPUT_CLEANUP',exit_status=0,removed=str(target),own_bytes_before=before,own_bytes_after=after,disk_free_after_bytes=shutil.disk_usage(B).free,key_files_found=0,non_key_placeholder_directories=[str(p) for p in B.rglob('*keypair*.json') if p.is_dir()],retained='source tree, ELF artifacts, diagnostics, receipts and runner scripts',wall_seconds=time.monotonic()-t,peak_rss_kib=r.ru_maxrss,swaps=r.ru_nswap,print_axioms='N/A: Python hygiene only; no build/test scope')
(B/'NKX_CLEANUP.json').write_text(json.dumps(x,indent=1)+'\n');print(json.dumps(x))
