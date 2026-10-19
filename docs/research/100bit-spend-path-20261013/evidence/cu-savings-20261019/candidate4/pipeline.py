#!/usr/bin/env python3
from pathlib import Path
import argparse,json,subprocess,hashlib,re,shutil,gzip,tarfile
p=argparse.ArgumentParser();p.add_argument('candidate',type=int);p.add_argument('revision');a=p.parse_args();n=a.candidate;rev=a.revision;w=Path('/home/dombarker/project-offloads/aspis-r1-cu-savings-20261019')
if n==2:
 for tree in ['clean','injections','sbf']:
  shutil.copy2(w/'program-Cargo.toml',w/tree/'programs/r1-cost-probe/Cargo.toml')
  for name in ['lib.rs','r1_pool_adapter.rs']:shutil.copy2(w/name,w/tree/'programs/r1-cost-probe/src'/name)
if n==3:
 for tree in ['clean','injections','sbf']:shutil.copy2(w/'weights.rs',w/tree/'crates/aspis-r1-cost-probe/src/weights.rs')
if n==4:
 for tree in ['clean','injections','sbf']:shutil.copy2(w/'fast_dots.rs',w/tree/'crates/aspis-r1-cost-probe/src/fast_dots.rs')
# Freeze each source snapshot independently, including all test overlays.
manifest={str(p.relative_to(w)):hashlib.sha256(p.read_bytes()).hexdigest() for tree in ['clean','injections','sbf'] for p in (w/tree).rglob('*') if p.is_file()}
(w/f'candidate{n}-inputs.json').write_text(json.dumps({'revision':rev,'files':manifest},indent=2)+'\n')
def run(label,plan):
 plan['source_revision']=rev;plan['out']=str(w/'runs'/f'c{n}-{label}')
 receipt=Path(plan['out'])/'receipt.json'
 if receipt.exists():
  prior=json.loads(receipt.read_text());assert prior['source_revision']==rev and prior['exit_status']==0;print(f'c{n} {label}: retain successful existing receipt',flush=True);return prior
 path=w/f'c{n}-{label}.json';path.write_text(json.dumps(plan,indent=2)+'\n')
 with (w/f'c{n}-{label}-launch.log').open('w') as f:
  code=subprocess.run(['systemd-run','--user','--scope',f'--unit=r1-cu-c{n}-{label}','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','python3',str(w/'run.py'),str(path)],stdout=f,stderr=subprocess.STDOUT).returncode
 print(f'c{n} {label} exit={code}',flush=True);assert code==0,(label,code)
 return json.loads((Path(plan['out'])/'receipt.json').read_text())
if n==3:
 plan=json.loads((w/'injections-default.json').read_text());plan['command'][plan['command'].index('decision1h')]='all_s2_inactive_table_entries_match_reference';run('focused-mask-table',plan)
if n==4:
 plan=json.loads((w/'injections-default.json').read_text());plan['cwd']=str(w/'clean');plan['command']=['/home/dombarker/.cargo/bin/cargo','test','--verbose','--release','--locked','--offline','-j1','-p','aspis-r1-cost-probe','--features','private-leaf-salts,optimized-terminal','--test','dots_equivalence','--','--test-threads=1'];run('focused-dots',plan)
for label in ['codec','counter','checkpoint','injections-default','injections-detail']:
 plan=json.loads((w/(label+'.json')).read_text())
 if label=='counter':plan['command'][-2:]=[str(w/f'candidate{n}-ordered.json'),rev]
 run(label,plan)
b=Path('/home/dombarker/project-offloads/aspis-r1-worker-b-1h-native-20261019');ib=Path('/home/dombarker/project-offloads/aspis-r1-worker-b-1h-injection-20261019');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(w/f'runs/c{n}-codec/stdout.log')==sha(b/'baselines/codec1233.stdout.log')
x=json.loads((w/f'candidate{n}-ordered.json').read_text());z=json.loads((b/'ordered-counter-no-prover.json').read_text())
for d in [x,z]:d['hash_input_counts']['repeated_exact_inputs'].sort(key=lambda x:x['input_hex'])
for k in x:
 if 'revision' not in k:assert x[k]==z[k],k
assert '23 passed; 0 failed' in (w/f'runs/c{n}-checkpoint/stdout.log').read_text()
for label in ['default','detail']:
 out=(w/f'runs/c{n}-injections-{label}/stdout.log').read_text();assert '3 passed; 0 failed' in out
 base=(ib/f'runs/injection-no-prover-1h-{label}/stdout.log').read_text();records=lambda s:[x[x.index('{'):] for x in s.splitlines() if '{' in x];assert records(out)==records(base),label
(w/f'candidate{n}-native-validation.json').write_text(json.dumps({'codec_outputs':1233,'codec_byte_identical':True,'ordered_trace_identical':True,'ordered_counts':[349,234],'checkpoint_tests':23,'injections_default_and_detail_records_byte_identical':True},indent=2))
plan=json.loads((w/'sbf.json').read_text());plan['command'][plan['command'].index('--sbf-out-dir')+1]=str(w/f'candidate{n}-artifacts');run('sbf',plan)
out=w/f'candidate{n}-stack';out.mkdir();shutil.copy2(Path(plan['env']['CARGO_TARGET_DIR'])/'sbpf-solana-solana/release/aspis_r1_cost_probe_program.so',out/'linked.elf');shutil.copy2(w/f'candidate{n}-artifacts/aspis_r1_cost_probe_program.so',out/'stripped.so');(out/'build.log').write_bytes((w/f'runs/c{n}-sbf/stdout.log').read_bytes()+(w/f'runs/c{n}-sbf/stderr.log').read_bytes())
plan=json.loads((w/'stack.json').read_text());plan['command'][-1]=str(out);run('stack',plan)
assert json.loads((out/'stack-audit.json').read_text())['gate_pass']
for flow in ['transfer','withdrawal']:
 for pairs in [13,255,1023]:
  label=f'{flow}-{pairs}';plan=json.loads((w/(label+'.json')).read_text());cmd=plan['command'];cmd[2]=str(w/f'candidate{n}-artifacts/aspis_r1_cost_probe_program.so');cmd[4]=str(w/f'candidate{n}-{label}-evidence.json');cmd[5]=str(w/f'candidate{n}-{label}-task');run(label,plan)
# Collect only receipts/logs and public runtime evidence, never task directories or keys.
out=w/f'candidate{n}-evidence';out.mkdir(exist_ok=True)
for p in w.glob(f'runs/c{n}-*'):
 target=out/'runs'/p.name;target.mkdir(parents=True,exist_ok=True)
 for f in p.iterdir():
  if f.suffix=='.log' and f.stat().st_size>1000000:
   with f.open('rb') as src,gzip.open(target/(f.name+'.gz'),'wb') as dst:shutil.copyfileobj(src,dst)
  else:shutil.copy2(f,target/f.name)
for f in [f'candidate{n}-inputs.json',f'candidate{n}-native-validation.json','run.py','strict-stack.py','pipeline.py']:shutil.copy2(w/f,out/f)
shutil.copy2(w/f'candidate{n}-stack/stack-audit.json',out/'stack-audit.json')
baseline={'transfer-13':(1340982,1329117),'transfer-255':(1340886,1366325),'transfer-1023':(1340971,1363282),'withdrawal-13':(1339489,1342661),'withdrawal-255':(1339527,1380079),'withdrawal-1023':(1339699,1376825)};rows=[]
for p in sorted(w.glob(f'candidate{n}-*-evidence.json')):
 d=json.loads(p.read_text());e=d['execution'];label=p.name[len(f'candidate{n}-'):-len('-evidence.json')];assert e['error'] is None and e['stage1_error'] is None
 nested=[int(m[1]) for l in e['logs'] if (m:=re.search(r'Program 7Q2.* consumed (\d+) of',l))];assert len(nested)==1;old1,old2=baseline[label];rows.append({'case':label,'stage1_transaction_cu':e['stage1_compute_units'],'nested_stage2_cu':nested[0],'settlement_transaction_cu':e['compute_units'],'stage1_saving_from_J1R13':old1-e['stage1_compute_units'],'settlement_saving_from_J1R13':old2-e['compute_units']});shutil.copy2(p,out/p.name)
summary={'candidate':n,'source_revision':rev,'candidate_elf_sha256':sha(w/f'candidate{n}-artifacts/aspis_r1_cost_probe_program.so'),'features':['pool-adapter','private-leaf-salts'],'measurements':rows,'remaining_gaps_1200000':{'stage1':max(x['stage1_transaction_cu'] for x in rows)-1200000,'settlement':max(x['settlement_transaction_cu'] for x in rows)-1200000},'keys':'All runtime task/key directories retained on NUC, never copied to evidence. No network transactions.','print_axioms':'N/A: no Lean compiled'}
(out/'SUMMARY.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary),flush=True)
with tarfile.open(w/f'candidate{n}-evidence.tar.gz','w:gz') as t:t.add(out,arcname=f'candidate{n}')
