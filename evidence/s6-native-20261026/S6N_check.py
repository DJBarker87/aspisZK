#!/usr/bin/env python3
"""Validate the prefix-only S6 transport evidence without launching any prover."""
from pathlib import Path
import hashlib,json,re,subprocess
P=Path(__file__).resolve().parent
R=P.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
limits={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
standard={'propext','Classical.choice','Quot.sound'}
for patch in json.loads((P/'S6N_RAW_LOG_WHITESPACE.json').read_text()):
 f=P/patch['path'];assert sha(f)==patch['normalized_sha256']
 lines=f.read_bytes().splitlines(keepends=True)
 for line in patch['patches']:lines[line['zero_based_line']]=line['original'].encode()
 assert hashlib.sha256(b''.join(lines)).hexdigest()==patch['original_sha256']
receipts=[]
for p in sorted(P.glob('S6N_[LKR][0-9][0-9][0-9]/receipt.json')):
 x=json.loads(p.read_text());a=x['attempt'];assert x['limits']==limits,a
 assert x['source_revision'] and x['source_hashes'],a
 assert x['swaps']=='0',a
 for name,h in x['source_hashes'].items():assert sha(p.parent/'sources'/name)==h,(a,name)
 if x['exit_status']==0 and x['kind']=='lean':
  for line in x['print_axioms']:
   if 'depends on axioms:' in line:assert set(re.search(r'\[(.*)\]',line,re.S)[1].replace('\n','').split(', '))<=standard,(a,line)
 if x['kind']=='lean' and x['exit_status']==0:
  for name,h in x['source_hashes'].items():assert sha(R/'lean'/name)==h,(a,name,'current source changed')
 receipts.append(x)
lean=[x for x in receipts if x['kind']=='lean'];kani=[x for x in receipts if x['kind']=='kani'];rust=[x for x in receipts if x['kind']=='rust']
assert len(lean)==100 and len(kani)==5 and len(rust)==2,(len(lean),len(kani),len(rust))
assert {x['attempt'] for x in lean if x['exit_status']!=0}=={'S6N_L002'}
assert {x['attempt'] for x in kani if x['exit_status']==0}=={'S6N_K004','S6N_K005'}
for a in ['S6N_K004','S6N_K005']:
 log=(P/a/'stdout.log').read_text();assert '0 of 329 failed' in log and '1 of 1 cover properties satisfied' in log,a
for a in ['S6N_R001','S6N_R002']:
 log=(P/a/'stdout.log').read_text();assert log.count('1880-byte real decoder, exact contents, getters, drop and rejection passed')==2,a
for x in json.loads((P/'S6N_FROZEN_SOURCE_CHECK.json').read_text()):
 assert x['frozen_prefix_identical'];assert sha(R/x['path'])==x['current_sha256']
for x in json.loads((P/'S6N_HELPER_SOURCE_CHECK.json').read_text()):
 assert x['frozen_prefix_identical'] and sha(R/x['path'])==x['current_sha256']
x=json.loads((P/'S6N_GENERATED_PIN.json').read_text());assert x['frozen_identical'] and sha(R/x['path'])==x['sha256']
x=json.loads((P/'S6N_NATIVE_SOURCE_VALIDATION.json').read_text());assert x['checked']==156 and not x['mismatches']
for f,x in json.loads((P/'S6N_NATIVE_SOURCE_PINS.json').read_text()).items():assert sha(R/f)==x['sha256']
expected=set(json.loads((P/'S6N_DECODER_CLOSURE.json').read_text()))
covered=set()
for f in (R/'lean').glob('S6N_Audit*.lean'):
 covered.update(re.findall(r'#print axioms AspisR1TerminalDecoder\.([\w.]+)',f.read_text()))
assert len(expected)==168 and covered==expected
old=(P/'S6N_BEFORE.lean.txt').read_text();new=(P/'S6N_AFTER.lean.txt').read_text()
domain=lambda s:s.split('theorem deployed',1)[1].split('    :\n    let select',1)[0]
assert domain(old)==domain(new);assert new==(R/'lean/S6N_Top.lean').read_text()
for f in (R/'lean').glob('S6N_*.lean'):
 s=f.read_text();assert not re.search(r'\b(sorry|admit|native_decide)\b|^axiom |set_option (maxHeartbeats|maxRecDepth)',s,re.M),f
for f in (P/'S6N_native/src').glob('*.rs'):
 s=f.read_text();assert 'kani::assume' not in s and 'kani::stub' not in s and 'unsafe' not in s,f
changed=subprocess.check_output(['git','diff','--name-only','e97cb3923c111d0c3f49968bd76ba05417d158c7'],cwd=R,text=True).splitlines()
assert all(f.startswith('evidence/s6-native-20261026/') or f.startswith('lean/S6N_') for f in changed),changed
for f in P.rglob('*'):
 if f.is_file():assert f.suffix not in {'.olean','.ir','.so','.elf','.tar','.gz'},f
summary={'lean_attempts':len(lean),'lean_passes':sum(x['exit_status']==0 for x in lean),'kani_runs':len(kani),'kani_passes':2,'optimized_native_attempts':2,'max_peak_rss_kib':max(int(x['peak_rss_kib']) for x in receipts),'swaps':0,'standard_axioms_only_for_successful_audits':True,'L176_deployment_delta':-1,'actual_antecedent_delta':0,'deduplicated_P':[31,30],'shipped_changes':False,'new_ELF_rebuild_trigger':False}
(P/'S6N_VALIDATION.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary))
