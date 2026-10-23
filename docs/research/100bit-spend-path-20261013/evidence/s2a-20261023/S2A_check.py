#!/usr/bin/env python3
"""Final source/receipt/axiom audit. No solver, compilation or release claim."""
from pathlib import Path
import json,re,hashlib,subprocess
E=Path(__file__).resolve().parent; B=E.parents[1]; R=E.parents[4]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
acceptedLean=['lean-001','lean-003','lean-007','lean-010','lean-011','lean-013']
acceptedNative={'kani-011':'S2A-native-gate-window0-v2','kani-012':'S2A-native-gate-window1-v2','kani-015':'S2A-native-gate-tail0-v3','kani-016':'S2A-native-gate-tail1-v3'}
standard={'propext','Classical.choice','Quot.sound'}
records=[]
for p in sorted(E.glob('*/receipt.json')):
 r=json.loads(p.read_text()); a=r['attempt']
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert int(r['swaps'])==0
 for required in ['source_revision','command','source_hashes','deps_fingerprint','exit_status','wall_seconds','peak_rss_kib','print_axioms']:assert required in r,(a,required)
 status='excluded'
 if a in acceptedLean:
  assert r['exit_status']==0 and r['print_axioms']
  for line in r['print_axioms']:
   if 'does not depend on any axioms' in line:continue
   m=re.search(r'depends on axioms:\s*\[([^]]*)\]',line); assert m,line
   assert set(re.findall(r'[\w.]+',m[1]))<=standard,line
  status='accepted focused Lean'
 elif a in acceptedNative:
  assert r['exit_status']==10
  audit=json.loads((E/acceptedNative[a]/'audit.json').read_text());assert audit['required_failures']==0 and len(audit['reached_entry_covers'])==2
  status='accepted native open-cut gate; raw exit10 covers/reachability only'
 elif a in ['kani-003','kani-008']:
  assert r['exit_status']==0;status='accepted bounded spec gate'
 elif a in ['kani-007','kani-010','kani-014']:
  assert r['exit_status']==0;status='codegen only; no proof credit'
 elif a=='lean-009':status='superseded successful source version'
 records.append({'attempt':a,'classification':status,'receipt':str(p.relative_to(E)),'receipt_sha256':sha(p),'exit_status':r['exit_status'],'wall_seconds':r['wall_seconds'],'peak_rss_kib':r['peak_rss_kib'],'swaps':r['swaps'],'source_revision':r['source_revision'],'source_hashes':r['source_hashes'],'deps_fingerprint':r['deps_fingerprint'],'print_axioms':r['print_axioms']})
last=json.loads((E/'lean-013/receipt.json').read_text());assert len(last['print_axioms'])==14
for name,h in last['source_hashes'].items():
 p=B/'lean'/name;assert sha(p)==h
 data=subprocess.check_output(['git','show',last['source_revision']+':'+str(p.relative_to(R))],cwd=R);assert hashlib.sha256(data).hexdigest()==h
for p in (B/'lean').glob('S2A_*.lean'):
 assert not re.search(r'\b(sorry|admit|native_decide)\b|^\s*(axiom|opaque)\s|set_option\s+(maxHeartbeats|maxRecDepth)',p.read_text(),re.M),p
for p in E.rglob('*'):
 if p.is_file():assert p.suffix not in ['.olean','.out','.o','.rlib','.so','.dylib','.elf','.tar','.gz','.pyc'],p
initial=json.loads((E/'stage0.json').read_text())
for p,h in initial['source_pins'].items():assert sha(R/p)==h,(p,'frozen source changed')
changed=subprocess.check_output(['git','diff','--name-only','0accd8700d893bc85f8be7b201143fd95aeb7a19','HEAD'],cwd=R,text=True).splitlines()
allowed=['docs/research/100bit-spend-path-20261013/evidence/s2a-20261023/','docs/research/100bit-spend-path-20261013/lean/S2A_','docs/research/100bit-spend-path-20261013/design/S2A-20261023.md']
assert all(any(p.startswith(a) for a in allowed) for p in changed)
assert len([r for r in records if r['attempt'].startswith('lean-')])==13
assert len([r for r in records if r['attempt'].startswith('kani-')])==15
summary={'schema':'focused-extractor-proof-packet-v1','status':'partial; common native E certificate NOT established; S2 OPEN','source_revision_of_final_theorem_audit':last['source_revision'],'accepted_lean':acceptedLean,'accepted_native_open_cuts':acceptedNative,'accepted_spec':['kani-003','kani-008'],'budget':{'lean_attempts':13,'lean_limit':100,'kani_proof_codegen_cbmc_invocations':15,'kani_help_inspections':1,'charged_kani':16,'kani_limit':60,'unlaunched_configs':['kani-002']},'new_trust_items':[],'retained_trust':'Only the adopted fifteen SDK fields, as explicit hypotheses; no production Library instance established','shipped_source_changes':False,'elf_rebuilds':False,'same_E_certificate_exists':False,'complete_E_indexed_ready_inputs_exported':False,'final_public_axiom_reports':last['print_axioms'],'records':records}
(E/'manifest.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps({'status':summary['status'],'budget':summary['budget'],'accepted_native_windows':4,'final_public_axiom_reports':14,'shipped_source_changes':False}))
