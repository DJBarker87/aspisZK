from pathlib import Path
import json,lzma,hashlib,re,subprocess,difflib
E=Path(__file__).resolve().parent
sha=lambda x:hashlib.sha256(x).hexdigest()
records=[json.loads(l) for l in (E/'NKF_ATTEMPTS.jsonl').read_text().splitlines()]
base_path=E.parent/'ledger17-20261108/NKC_LEDGER.json.xz';base_raw=lzma.decompress(base_path.read_bytes());base=json.loads(base_raw)
ids=['TX2:216','TX2:217','TX2:218','TX2:233','TX2:234','TX2:242'];byid={r['row']:r for r in base['rows']}
assert len(base['rows'])==599 and all(byid[i]['status']=='OPEN' for i in ids)
native=[]
for r in records:
 if r['kind']!='kani':continue
 a=r['attempt'];t=lzma.decompress((E/a/'stdout.log.xz').read_bytes()).decode()
 native.append(dict(attempt=a,target=r['module'],exit=r['exit_status'],invoked=(E/(a+'-lock-check.json')).exists(),timeout='CBMC timed out' in t,unwind='Failed Checks: unwinding' in t,compile_error='error: could not compile' in t,semantic_failure='Failed Checks:' in t and 'CBMC timed out' not in t and 'Failed Checks: unwinding' not in t,excluded_pass=a in ['NKF_K066','NKF_K080']))
assert len(native)==80 and sum(x['invoked'] for x in native)==79
(E/'NKF_NATIVE_RESULTS.json').write_text(json.dumps(native,indent=1)+'\n')
current=[];roots=[]
for p in sorted(E.glob('NKF_*.lean')):
 if p.stem in ['NKF_COMBINED_IMPORT','NKF_ScanDriver']:continue
 h=sha(p.read_bytes());rs=[r for r in records if r['kind']=='lean' and r['module']==p.stem and r['exit_status']==0 and h in r['source_hashes'].values()]
 assert rs,p.name
 r=rs[-1];t=lzma.decompress((E/r['attempt']/'stdout.log.xz').read_bytes()).decode()
 assert 'sorryAx' not in t,p.name
 ns=re.search(r'^namespace (\w+)',p.read_text(),re.M)[1]
 names=[ns+'.'+n for n in re.findall(r'^theorem (\w+)',p.read_text(),re.M)]
 for n in names:
  assert "'"+n+"'" in t,(p,n)
  roots.append(n)
 lines=[l for l in t.splitlines() if 'depends on axioms' in l or 'does not depend on any axioms' in l]
 for line in lines:
  m=re.search(r'depends on axioms: \[(.*)\]',line)
  if m:assert set(m[1].split(', '))<={'propext','Classical.choice','Quot.sound'}
 current.append(dict(module=p.stem,source_sha256=h,attempt=r['attempt'],roots=names,axioms=lines,status='FOCUSED_COMPILED_STANDARD_AXIOMS_ONLY'))
(E/'NKF_FOCUSED_FORMAL.json').write_text(json.dumps(current,indent=1)+'\n')
# Save every authored harness as a reproducible patch once per input hash.
idx=json.loads((E/'NKF_INPUTS.json').read_text());patches={};D=E/'NKF_PATCHES';D.mkdir(exist_ok=True)
for a,inputs in idx['attempts'].items():
 for n,h in inputs.items():
  if not n.startswith('NKF_src/') or not n.endswith('.rs') or not Path(n).name.startswith('NKF_'):continue
  raw=lzma.decompress((E/idx['objects'][h]['path']).read_bytes());assert sha(raw)==h
  p=D/(h+'.patch')
  if not p.exists():
   text=raw.decode();p.write_text('--- /dev/null\n+++ b/'+n[8:]+'\n@@ -0,0 +1,'+str(len(text.splitlines()))+' @@\n'+''.join('+'+l for l in text.splitlines(True)))
  patches.setdefault(a,[]).append(dict(path=n,input_sha256=h,patch=str(p.relative_to(E)),patch_sha256=sha(p.read_bytes())))
(E/'NKF_PATCH_INDEX.json').write_text(json.dumps(patches,indent=1)+'\n')
for p in E.glob('NKF_*.rs'):
 text=p.read_text();p.with_suffix('.patch').write_text('--- /dev/null\n+++ b/'+p.name+'\n@@ -0,0 +1,'+str(len(text.splitlines()))+' @@\n'+''.join('+'+l for l in text.splitlines(True)));p.unlink()
infra=dict(status='STOP_SHARED_ADMISSION',attempt='NKF_K081',submitted=False,reservation_exit_codes=[120,120],reservation_json='zero-byte file; no valid JSON',logs=['NKF_K081-barrier-0.log','NKF_K081-barrier-1.log'],retry='one30-second missing-receipt retry used',required_admission='exit0 AND allowed:true',rule='local-lean.txt rules5/7/9',read_only_recovery='NKF_INFRASTRUCTURE_RECOVERY.json',no_resume_or_bypass=True)
(E/'NKF_INFRASTRUCTURE_STOP.json').write_text(json.dumps(infra,indent=1)+'\n')
opens=[]
for i in ids:
 r=byid[i];opens.append(dict(row=i,function=r['function'],status='OPEN',frozen_body_sha256=r['frozen_body_sha256'],obligation_statement_hash=r['obligation_statement_hash']))
(E/'NKF_CLOSED.json').write_text(json.dumps(dict(frozen_revision=base['frozen_revision'],headline='AspisR1.RPx_Deployed.deployed',functions=[],open_functions=opens,admission='NONE: combined import/NFX/raw-ax2 not run',status='NO_CLOSED_ROWS_INFRASTRUCTURE_STOP',validation='Focused native/model support only; no leaf or parent promoted'),indent=1)+'\n')
(E/'NKF_LEDGER_DELTA.json').write_text(json.dumps(dict(baseline='evidence/ledger17-20261108/NKC_LEDGER.json.xz',baseline_archive_sha256=sha(base_path.read_bytes()),baseline_uncompressed_sha256=sha(base_raw),before=dict(CLOSED=514,QUALIFIED=0,OPEN=85,total=599),after=dict(CLOSED=514,QUALIFIED=0,OPEN=85,total=599),changes=[],owned_rows=ids,status='NO_DELTA_UNGATED',security_target_established=False),indent=1)+'\n')
resources=dict(scopes=len(records),native_scopes=len(native),kani_invocations=79,kani_authorized=80,kani_unsubmitted='NKF_K081',lean_attempts=sum(r['kind']=='lean' for r in records),lean_authorized=90,extractor_invocations=1,extractor_authorized=1,extraction_validation_only='NKF_L001',wall_seconds=sum(float(r['wall_seconds']) for r in records),peak_rss_kib=max(int(r['peak_rss_kib']) for r in records),swaps=sum(int(r['swaps']) for r in records),limits=dict(MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=64),one_scope_at_a_time=True,Lean_M=7000)
(E/'NKF_RESOURCE_INDEX.json').write_text(json.dumps(resources,indent=1)+'\n')
(E/'NKF_AUDIT.json').write_text(json.dumps(dict(status='NOT_GATED_INFRASTRUCTURE_STOP',combined_import='NKF_COMBINED_IMPORT.lean prepared, NOT compiled',combined_audits_run=0,combined_audits_limit=2,nfx_scan='NOT_RUN',raw_ax2='NOT_RUN',headline_replay='NOT_RUN',current_focused_modules=len(current),current_focused_top_theorems=len(roots),focused_axioms='subset of propext/Classical.choice/Quot.sound; complete lines in NKF_FOCUSED_FORMAL.json and receipts',excluded_failed_formal_attempts=['NKF_L003','NKF_L008'],ungated_rows=ids,resources=resources,standard_axioms_do_not_imply_native_association=True,security_target_established=False),indent=1)+'\n')
(E/'NKF_UNRUN.json').write_text(json.dumps(dict(native=['NKF_K081: repaired ordinary constructor-oracle Box controls plus corrected seed-frame mutation; no admission, no upload/submission'],lean=['NKF_SeedWindows.lean.wip: three helper statements, NOT compiled'],combined=['NKF_COMBINED_IMPORT','raw ax2 all35listed roots including headline','NFX module/owner scan','full selected closure comparison to NKC'],reason=infra),indent=1)+'\n')
# Section6 source/artifact facts, without pretending to have rebuilt ELFs.
rc=subprocess.run(['git','diff','--quiet','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387','HEAD','--','crates','programs','Cargo.lock']).returncode
assert rc==0
(E/'NKF_RELEASE_PINS.json').write_text(json.dumps(dict(frozen_revision=base['frozen_revision'],features='pool-adapter,private-leaf-salts; full per-crate resolved features in every native graph check',wire_format='frozen release unchanged',crates_programs_lock_byte_identical=True,elf_rebuild_trigger=False,elf_hashes_inherited_not_reproduced=dict(default='f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4',devnet='63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299',Pool='121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548'),contract='Frozen3; deployed headline; L154 parameter; narrowed D188;100-bit PER-ATTEMPT/privacy/two transactions unchanged',trust='no added/removed trust rows; P6/D188 transport retained; no admitted NKF ReviewedTranscription item'),indent=1)+'\n')
print(json.dumps(dict(status='NO_PROMOTIONS',focused_modules=len(current),focused_theorems=len(roots),resources=resources)))
