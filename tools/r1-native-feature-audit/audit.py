#!/usr/bin/env python3
"""Audit accepted native gate features from Git archive bytes; never runs Cargo."""
import argparse,hashlib,io,json,re,shlex,subprocess,tarfile,tomllib
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2];BASE='docs/research/100bit-spend-path-20261013/evidence/';OUT=ROOT/BASE/'native-feature-coverage-20261018';sha=lambda b:hashlib.sha256(b).hexdigest()
SPECS=[('clean','final-a555-clean-native-20261017/final-a555-clean-native.tar.gz','source-clean/', [('codec1233-final','runs/codec1233-final/','aspis_statement'),('saved-proof-counter-final','runs/saved-proof-counter-final/','aspis_r1_cost_probe'),('checkpoint23-final','runs/checkpoint23-final/','aspis_r1_cost_probe')]),('injection','verify-query-native-20261017/native-evidence.tar.gz',None,[('verify-real-s2-default','verify-final/runs/verify-real-s2-default/','aspis_r1_cost_probe'),('verify-real-s2-detail','verify-final/runs/verify-real-s2-detail/','aspis_r1_cost_probe'),('query-migration-102','query/runs/query-migration-102/','aspis_r1_cost_probe')])]
def git(ref,path):return subprocess.check_output(['git','-C',str(ROOT),'show',ref+':'+path])
def cfgs(line):
 cmd=shlex.split(line.split('Running `',1)[1].rsplit('`',1)[0]);features=[];ext={}
 for i,t in enumerate(cmd[:-1]):
  if t=='--cfg':
   m=re.fullmatch(r'feature="([^"]+)"',cmd[i+1])
   if m:features.append(m[1])
  if t=='--extern':
   name,_,path=cmd[i+1].partition('=');ext[name]=path
 return {'command':cmd,'active_cfg_features':sorted(features),'externs':ext,'raw_running_line':line,'check_cfg_values_are_enabled_features':False}
def build(ref):
 full=subprocess.check_output(['git','-C',str(ROOT),'rev-parse',ref],text=True).strip();report={'classification':'READ_ONLY_ARCHIVED_NATIVE_FEATURE_AUDIT','audited_revision':full,'archives':{},'gates':[],'new_builds':0}
 for label,path,pre,gates in SPECS:
  raw=git(full,BASE+path);t=tarfile.open(fileobj=io.BytesIO(raw));read=lambda n:t.extractfile(n).read();report['archives'][label]={'git_path':BASE+path,'sha256':sha(raw),'bytes':len(raw)}
  for gate,run,primary in gates:
   prefix=pre or ('query/source/' if gate.startswith('query') else 'verify-final/source/');rr=read(run+'receipt.json');r=json.loads(rr);stderr=read(run+'stderr.log');stdout=read(run+'stdout.log');assert sha(stderr)==r['stderr_sha256'] and sha(stdout)==r['stdout_sha256'];assert sha(read(run+'runner.py'))==r['runner_sha256'];assert sha(read(run+'input-manifest.json'))==r['input_manifest_sha256'];assert r['exit_status']==0
   manifests={}
   for f in ['Cargo.toml','crates/aspis-r1-cost-probe/Cargo.toml','crates/aspis-statement/Cargo.toml','programs/r1-cost-probe/Cargo.toml','tools/r1-hash-input-counter/Cargo.toml']:
    b=read(prefix+f);d=tomllib.loads(b.decode());manifests[f]={'member':prefix+f,'sha256':sha(b),'text':b.decode(),'parsed':d}
   invocations=[]
   for line in stderr.decode().splitlines():
    if 'Running `' in line and '--crate-name ' in line and any('--crate-name '+n+' ' in line for n in ['aspis_r1_cost_probe','aspis_r1_cost_probe_program','aspis_statement','aspis_prover']):invocations.append(cfgs(line))
   selected=[c for c in invocations if c['command'][c['command'].index('--crate-name')+1]==primary];assert len(selected)==1,(gate,len(selected))
   pc=selected[0];cost=next((c for c in invocations if c['command'][c['command'].index('--crate-name')+1]=='aspis_r1_cost_probe'),None)
   command=r['command'];explicit=command[command.index('--features')+1].split(',') if '--features' in command else []
   features=sorted(cost['active_cfg_features']) if cost else None
   item={'gate':gate,'archive':label,'receipt_member':run+'receipt.json','receipt_sha256':sha(rr),'receipt':r,'environment':json.loads(read(run+'environment.json')),'explicit_Cargo_features':explicit,'Cargo_no_default_features':'--no-default-features' in command,'cost_probe_default_features':manifests['crates/aspis-r1-cost-probe/Cargo.toml']['parsed']['features']['default'],'effective_cost_probe_features':features,'effective_cost_probe_prover':('prover' in features) if features is not None else 'NOT_IN_GATE_DEPENDENCY_COMPILE','effective_selected_rustc':pc,'relevant_rustc_invocations':invocations,'source_manifests':manifests,'runner_member':run+'runner.py','runner_sha256':r['runner_sha256'],'stderr_member':run+'stderr.log','stderr_sha256':sha(stderr),'evidence_basis':'Actual archived rustc --cfg feature arguments and --extern dependency edges, checked against pinned source manifests. --check-cfg permitted values are NOT enabled features.'}
   if gate=='codec1233-final':item['resolution']='Selected statement rustc cfg only pool-v1-kernel,r0. No cost-probe crate in this gate; this is a codec gate, not verifier feature coverage.'
   elif gate=='saved-proof-counter-final':
    assert 'prover' in features and 'aspis_prover' in cost['externs'];assert 'prover' in manifests['tools/r1-hash-input-counter/Cargo.toml']['parsed']['dependencies']['aspis-r1-cost-probe']['features'];item['resolution']='Standalone counter dependency explicitly enables cost-probe/prover despite no Cargo --features flag. Actual cost-probe rustc cfg and linked aspis_prover confirm it.'
   elif gate=='checkpoint23-final':
    assert features==['default','optimized-terminal','private-leaf-salts'] and 'aspis_prover' not in cost['externs'];pr=next(c for c in invocations if c['command'][c['command'].index('--crate-name')+1]=='aspis_r1_cost_probe_program');assert pr['active_cfg_features']==['custom-heap','default','pool-adapter','private-leaf-salts'];assert 'prover' not in manifests['programs/r1-cost-probe/Cargo.toml']['parsed']['dependencies']['aspis-r1-cost-probe']['features'];item['resolution']='CONFIRMED WITHOUT cost-probe/prover. Program defaults custom-heap; dependency enables optimized-terminal; private-leaf-salts only forwards private-leaf-salts. Exact dependency artifact linked in program test rustc line.'
   else:
    assert 'prover' in features and 'aspis_prover' in cost['externs'];item['resolution']='CONFIRMED WITH cost-probe/prover; cannot establish no-prover verifier behavior.'
    path2='crates/aspis-r1-cost-probe/src/'+('transcript.rs' if gate.startswith('query') else 'r1_semantic.rs');body=read(prefix+path2).decode();module='query_migration_tests' if gate.startswith('query') else 'verify_migration_tests';lines=body.splitlines();idx=next(i for i,l in enumerate(lines) if l.strip()=='mod '+module+';' or l.strip().endswith('mod '+module+';'));item['test_module_gate']={'member':prefix+path2,'source_sha256':sha(body.encode()),'lines':[{'number':i+1,'text':lines[i]} for i in range(max(0,idx-2),idx+1)]}
   report['gates'].append(item)
 report['coverage_gap']='Checkpoint23 already confirms no-prover. Both accepted verify injection modes enable prover; modules are gated on prover. No-prover test-only overlay adaptation and explicit 112-case count per mode are required before claiming deployment-shape verify injection coverage. Query102 is also prover-enabled; no-prover query coverage is not established.'
 report['no_prover_verify_overlay_requirements']=['Remove prover condition only from test-module/old-body guards; keep test/private-leaf-salts restrictions.','Make returned diagnostic-only fields round_checks/terminal/masked_terminal conditional on prover, preserving every deployed-shape returned field.','Test-only std and SHA dependencies must be available without enabling cost-probe/prover or optional aspis_prover.','Production trace::value is a no-op without prover and trace::take absent: retain actual no-prover behavior, expose empty test snapshot only, and assert empty value log; preserve all call/digest/observer checks.','Run each default/detail mode with 56 cases times Some/None observers=112, explicit no-prover rustc cfg and absence of aspis_prover extern. Simply dropping --features prover would select zero injection tests.']
 return report
def main():
 p=argparse.ArgumentParser();p.add_argument('--ref',default='6dd9028e9');p.add_argument('--check',action='store_true');a=p.parse_args();d=(json.dumps(build(a.ref),sort_keys=True,indent=2)+'\n').encode();OUT.mkdir(parents=True,exist_ok=True);f=OUT/'feature-audit.json'
 if a.check:assert f.read_bytes()==d,'audit mismatch'
 else:f.write_bytes(d)
 print(json.dumps({'status':'PASS_READ_ONLY_FEATURE_AUDIT','report_sha256':sha(d),'gates':6,'checkpoint_no_prover':True,'verify_default_no_prover':False,'verify_detail_no_prover':False,'new_builds':0},sort_keys=True))
if __name__=='__main__':main()
