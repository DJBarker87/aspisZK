#!/usr/bin/env python3
"""Focused JSON/log packet checker; no build, source mutation or replay."""
import argparse,hashlib,importlib.util,io,json,subprocess,tarfile,tomllib
from pathlib import Path
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1];E=ROOT/'docs/research/100bit-spend-path-20261013/evidence/native-no-prover-20261018';REV='234a1431ba0ec533261864b6d34c86997c70239d';sha=lambda b:hashlib.sha256(b).hexdigest()
def read(p):return json.loads(p.read_text())
def main():
 p=argparse.ArgumentParser();p.add_argument('--packet',type=Path,default=E);a=p.parse_args();e=a.packet;m=read(e/'PACKET-MANIFEST.json');actual={str(p.relative_to(e)) for p in e.rglob('*') if p.is_file()}-{'PACKET-MANIFEST.json'};assert set(m['files'])==actual
 for name,h in m['files'].items():assert sha((e/name).read_bytes())==h,name;assert Path(name).suffix in ['.json','.log'],name
 invspec=importlib.util.spec_from_file_location('feature_audit',ROOT/'tools/r1-native-feature-audit/audit.py');f=importlib.util.module_from_spec(invspec);invspec.loader.exec_module(f)
 # Verify exact baseline Git bytes in one read-only cat-file batch.
 baseline=read(e/'counter-clean/source-audit.json')['Git_exact_source_files'];assert len(baseline)==532
 names=[i['path'] for i in baseline];raw=subprocess.check_output(['git','-C',str(ROOT),'cat-file','--batch'],input=''.join(REV+':'+n+'\n' for n in names).encode());stream=io.BytesIO(raw);gitsha={}
 for row in baseline:
  header=stream.readline().split();assert header[1]==b'blob';b=stream.read(int(header[2]));assert stream.read(1)==b'\n';assert sha(b)==row['sha256'],row['path'];gitsha[row['path']]=row['sha256']
 for alias,count in [('injections',10),('rejected-counter-injection-source',10),('counter-clean',3)]:
  audit=read(e/alias/'source-audit.json');overlay=read(e/alias/'overlay-source-inputs.json');state=read(e/alias/'snapshot-state.json');assert state['revision']==REV;assert len(overlay)==count;assert all(i['matches'] for i in state['files']);assert {i['path'] for i in audit['Git_exact_source_files']}==set(names)
  for name,item in overlay.items():assert sha(item['text'].encode())==item['current_sha256']==item['declared_sha256']
  expected={'source/'+n:h for n,h in gitsha.items()};expected.update({'source/'+n:i['current_sha256'] for n,i in overlay.items()});rows={i['path']:i for i in state['files'] if i['path'].startswith('source/')};assert set(rows)==set(expected)
  for n,h in expected.items():assert rows[n]['current_sha256']==h,(alias,n)
  if alias=='counter-clean':assert set(overlay)=={'tools/r1-hash-input-counter/Cargo.toml','tools/r1-hash-input-counter/Cargo.lock','tools/r1-hash-input-counter/src/main.rs'}
 reports={};cfgs={}
 for alias,label in [('injections','verify-no-prover-default'),('injections','verify-no-prover-detail'),('injections','query-no-prover-102'),('counter-clean','counter-no-prover-583')]:
  run=e/alias/'runs'/label;r=read(run/'receipt.json');reports[label]=r;assert r['exit_status']==r['process_swaps']==0;assert r['source_revision']==REV;assert r['cgroup_swap_current']=='0';assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0'}
  for field,file in [('stdout_sha256','stdout.log'),('stderr_sha256','stderr.log'),('input_manifest_sha256','input-manifest.json')]:assert r[field]==sha((run/file).read_bytes())
  assert r['runner_sha256']=='d011230e71adac99208489591e770e92744e53f9117be18060e315770866bb8c';g=read(e/alias/'governor'/(label+'-execute.json'));assert g['exit_status']==0 and g['status']=='OWN_JOB_EXITED';assert g['policy_override']['foreign_activity'].startswith('record only');assert g['aggregate_reservations']['admitted'] and g['immediately_before_spawn_reservations']['admitted'];assert int(g['cgroup_after']['memory.swap.current'])==0
  lines=[l for l in (run/'stderr.log').read_text().splitlines() if 'Running `' in l and '--crate-name aspis_r1_cost_probe ' in l]
  if label=='query-no-prover-102' and not lines:
   dr=reports['verify-no-prover-default'];assert r['input_manifest_sha256']==dr['input_manifest_sha256'];common={n:v for n,v in r['artifacts'].items() if n in dr['artifacts'] and v==dr['artifacts'][n] and '/deps/aspis_r1_cost_probe-' in n};assert len(common)==1;cfg=cfgs['verify-no-prover-default']
  else:assert len(lines)==1;cfg=f.cfgs(lines[0])
  cfgs[label]=cfg;assert 'prover' not in cfg['active_cfg_features'] and 'aspis_prover' not in cfg['externs'];expected=['default','private-leaf-salts'] if alias=='counter-clean' else ['default','optimized-terminal','private-leaf-salts']+(['detail-phases'] if label.endswith('detail') else []);assert cfg['active_cfg_features']==sorted(expected)
  text=(run/'stdout.log').read_text()
  if label.startswith('verify-'):
   cases=[l[l.index('VERIFY_REAL_S2_CASE '):] for l in text.splitlines() if 'VERIFY_REAL_S2_CASE ' in l];assert len(cases)==112;assert sum(' observed=false ' in l for l in cases)==56;assert sum(' observed=true ' in l for l in cases)==56;assert all('old_new_equal=true ' in l and 'trace_values=0 ' in l for l in cases);assert 'test result: ok. 1 passed; 0 failed;' in text;assert 'VERIFY_REAL_S2_PASS cases=112 faults=55 ' in text
  elif label.startswith('query-'):
   cases=[json.loads(l.split('QUERY_MIGRATION_CASE ',1)[1]) for l in text.splitlines() if 'QUERY_MIGRATION_CASE ' in l];assert len(cases)==102 and all(c['trace']==[] for c in cases);assert all(sum(c['context']==n for c in cases)==34 for n in ['saved-S2','synthetic-S1','synthetic-D']);assert 'test result: ok. 1 passed; 0 failed;' in text;assert 'QUERY_MIGRATION_PASS cases=102 ' in text
 # Pin comparison baseline to the previously accepted Git archive, not a new oracle.
 oldpath='docs/research/100bit-spend-path-20261013/evidence/final-a555-clean-native-20261017/final-a555-clean-native.tar.gz';oldraw=subprocess.check_output(['git','-C',str(ROOT),'show','6dd9028e9:'+oldpath]);t=tarfile.open(fileobj=io.BytesIO(oldraw));oldbytes=t.extractfile('ordered-counter.json').read();assert oldbytes==(e/'counter-clean/baseline-ordered-counter.json').read_bytes();old=json.loads(oldbytes);new=read(e/'counter-clean/ordered-counter-no-prover.json');assert new['source_revision']==REV;assert len(new['ordered_digest_calls'])==583 and new['ordered_digest_calls']==old['ordered_digest_calls'];assert new['acceptance']==old['acceptance'];assert new['hash_input_counts']['tx1_raw_calls']==349 and new['hash_input_counts']['tx2_raw_calls']==234
 ov=read(e/'counter-clean/overlay-source-inputs.json');locked=tomllib.loads(ov['tools/r1-hash-input-counter/Cargo.lock']['text']);before=subprocess.check_output(['git','-C',str(ROOT),'show',REV+':tools/r1-hash-input-counter/Cargo.lock']).decode();key=lambda p:(p['name'],p['version'],p.get('source'));bd={key(p):p for p in tomllib.loads(before)['package']};ad={key(p):p for p in locked['package']};assert all(k in bd and x.get('checksum')==bd[k].get('checksum') for k,x in ad.items());assert {k[0] for k in bd if k not in ad}=={'aspis-prover','getrandom','r-efi','wasip2','wit-bindgen','zeroize'}
 rejected=[('injections','counter-no-prover-583'),('rejected-counter-injection-source','counter-no-prover-583'),('lock-preparation','counter-lock-resolve')]
 for alias,label in rejected:assert read(e/alias/'runs'/label/'receipt.json')['exit_status']==101
 print(json.dumps({'status':'PASS_NO_PROVER_PACKET','revision':REV,'accepted_gates':4,'verify_cases_each':112,'query_cases':102,'ordered_calls':583,'tx1':349,'tx2':234,'Git_baseline_files':532,'injection_overlays':10,'clean_counter_tool_overlays':3,'retained_dependency_changes':0,'rejected_attempts_retained':3,'new_builds':0,'trace_values':'Production recording compiled out; explicitly empty snapshots; other actual observations compared.'},sort_keys=True))
if __name__=='__main__':main()
