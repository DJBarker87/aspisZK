"""Final local artifact/identity checks only; no proof replay."""
from pathlib import Path
import subprocess,json,hashlib,lzma,time,resource,sys,shutil
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;R=E.parents[1];start=time.monotonic();read=lambda p:json.loads(p.read_text());sha=lambda b:hashlib.sha256(b).hexdigest()
for script in ['NHY_certify.py','NHY_late_check.py']:
 r=subprocess.run([sys.executable,str(E/script)],capture_output=True,text=True);assert r.returncode==0,(script,r.stdout,r.stderr)
base=subprocess.check_output(['git','rev-parse','56662342da7^'],cwd=R,text=True).strip()
changed=set(subprocess.check_output(['git','diff','--name-only',base,'HEAD'],cwd=R,text=True).splitlines())|set(subprocess.check_output(['git','diff','--name-only','HEAD'],cwd=R,text=True).splitlines())|set(subprocess.check_output(['git','ls-files','--others','--exclude-standard'],cwd=R,text=True).splitlines())
assert all(p.startswith('evidence/slice-d-entry4-20261106/') for p in changed),sorted(changed)
assert not subprocess.check_output(['git','diff',base,'--','crates','programs','Cargo.lock'],cwd=R,text=True)
p=E/'NHY_HARNESS.patch';assert sha(p.read_bytes())==read(E/'NHY_PATCH_MANIFEST.json')['sha256'];r=subprocess.run(['git','apply','--check',str(p)],cwd=R,capture_output=True,text=True);assert r.returncode==0,r.stderr
io=read(E/'NHY_H001/receipt.json');ad=read(E/'NHY_H001-admission.json');assert io['exit_status']==0 and ad['exit']==0 and ad['reservation']['allowed'] is True
assert io['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'} and int(io['swaps'])==0
idx=read(E/'NHY_INPUTS.json')
for n,h in io['source_hashes'].items():assert idx['attempts']['NHY_H001'][n]==h
host=read(E/'NHY_HOST_FINAL.json');assert host['exit_status']==0 and not host['keys_deleted'] and not host['cache_deleted'];assert host['export']['read_only_dependencies_unchanged']
required=['SPINE.md','STUBS.md','BRIDGES.md','CANDIDATE_ROWS.md','CLOSED.json','EDGES.json','LEDGER_DELTA.json','AUDIT.json','COMBINED_IMPORT.lean','FAILING_STEP.md','HANDOFF.md','REMAINING.md','ATTEMPTS.jsonl']
assert all((E/('NHY_'+n)).is_file() for n in required)
# Every canonical current object has an exact successful-source receipt.
canon=read(E/'NHY_CANONICAL_MODULES.json');assert len(canon['modules'])==40
for item in canon['modules']:assert sha((E/(item['module']+'.lean')).read_bytes())==item['source_sha256']
roots=read(E/'NHY_AUDIT_ROOTS.json')['roots'];audit=read(E/'NHY_AUDIT.json');audited=json.dumps(audit['roots'])
assert all(root in audited for root in roots),[r for r in roots if r not in audited]
assert audit['scan']['dangling']==audit['scan']['incompatible_owners']==audit['scan']['import_mismatches']==0
assert read(E/'NHY_CLOSED.json')['new_composed_rows']==14 and read(E/'NHY_CLOSED.json')['new_composed_functions']==13
for p in E.rglob('__pycache__'):shutil.rmtree(p)
large=[str(p.relative_to(E)) for p in E.rglob('*') if p.is_file() and p.stat().st_size>20_000_000];assert not large,large
assert not [p for p in E.rglob('*') if p.is_file() and p.suffix in ['.olean','.ir','.o','.so','.elf','.out','.tar']]
out=dict(target='NHY final artifact/source/receipt/postflight, no proof replay',exit_status=0,wall_seconds=time.monotonic()-start,peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss//(1024 if sys.platform=='darwin' else 1),swaps=resource.getrusage(resource.RUSAGE_SELF).ru_nswap,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),source_tree_dirty=True,source_sha256=sha(Path(__file__).read_bytes()),print_axioms='Formal proof16 and all earlier raw groups in NHY_AUDIT.json; standard propext/Classical.choice/Quot.sound only',changed_files_only_own_evidence=True,shipped_source_unchanged=True,ELF_rebuild_triggered=False,required_outputs_present=True,canonical_modules=40,raw_roots=len(roots),files_over20MB=large,new_closed_rows=14,new_closed_functions=13,complete_TX1_paths=0,complete_TX2_paths=0,cache_retained=host['export']['directory'],cache_bytes=host['export']['total_bytes'],read_only_dependency_pins=host['export']['read_only_dependencies_verified'],keys_deleted=False,no_push=True)
(E/'NHY_POSTFLIGHT.json').write_text(json.dumps(out,indent=1)+'\n');print(json.dumps(dict(status='PASS_POSTFLIGHT',new_closed_rows=14,raw_roots=len(roots),canonical_modules=40)))
