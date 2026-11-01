"""Additive row packet audit. Does not modify NEB or promote composed rows."""
from pathlib import Path
import json,hashlib,re,copy,subprocess
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
obj=lambda p:json.loads(p.read_text())
def audit(E,R,packet,neb,require,function):
 require(packet['status']=='CLOSED-CONDITIONAL' and packet['route']=='D188_ACTUAL_BODY_ITERATOR_TRANSPORT','wrong row route')
 F='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
 require(packet['frozen_revision']==F and packet['suspended_neb_credits_restored']==[],'row frozen/trust drift')
 for item in packet['lean_evidence']:
  for theorem in item['theorems']:neb.check_receipt(item,theorem)
  d=obj(R/item['receipt'])
  for path,h in d['source_hashes'].items():require(sha(E/path.removeprefix('NEI_generated/'))==h,'row successful current source')
 old=E.parent/'slice-q-mul-20261029'
 # Byte-identical generated row body and carrier; external constructor repair
 # is explicitly interpreted, never silently erased.
 for n in ['Funs.lean','Types.lean']:
  require((old/'NEG_RowIsolated'/n).read_bytes()==(old/'NEG_extracted/NEG_RowIsolated'/n).read_bytes(),'edited inherited row output')
 require('into_iter_back back' in (old/'NEG_RowIsolated/Funs.lean').read_text(),'dropped row restoration')
 body=function(subprocess.check_output(['git','show',F+':crates/aspis-r1-cost-probe/src/verifier.rs'],cwd=R).decode(),'update_residue_row')
 require(hashlib.sha256(body[body.index('{'):].encode()).hexdigest()==packet['source_body_sha256'],'row frozen body hash')
 native=(E/'NEI_row_native.rs').read_text()
 source=subprocess.check_output(['git','show',F+':crates/aspis-r1-cost-probe/src/verifier.rs'],cwd=R).decode()
 for name in ['update_residue_row','residue_limb_at','power_limb_at']:require(function(native,name)==function(source,name),'native row isolation changed')
 caps=dict(zip(['memory.high','memory.max','memory.swap.max','pids.max'],['6442450944','8589934592','0','64']))
 for pos,neg,cfg in [('NEI_K010','NEI_K011','NEI_wrong_row_copy'),('NEI_K012','NEI_K013','NEI_wrong_iterator')]:
  ds=[obj(E/a/'receipt.json') for a in [pos,neg]]
  require([d['exit_status'] for d in ds]==[0,1],'row native/control verdict')
  require(ds[0]['source_hashes']==ds[1]['source_hashes'] and ds[0]['native_command']==ds[1]['native_command'],'native/control source mismatch')
  e=copy.deepcopy(ds[0]['env']);e['RUSTFLAGS']+=' --cfg '+cfg;require(e==ds[1]['env'],'native/control configuration mismatch')
  for a,d in zip([pos,neg],ds):
   require(d['limits']==caps and d['swaps']=='0','native row resource limits')
   require(d['copy_patch_sha256']=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67','wrong KMX')
   for n,h in d['source_hashes'].items():require(sha(E/a/'sources'/n)==h,'native archived source drift')
   require(obj(E/(a+'-graph-check.json'))['graph_matches_frozen'],'native graph drift')
   require(obj(E/(a+'-lock-check.json'))['unchanged'],'native lock drift')
   require(obj(E/(a+'-frozen-source-check.json'))['passed'],'native frozen body drift')
   require(obj(E/(a+'-rule16-check.json'))['static_declarations']==[],'native writable static')
   require(obj(E/(a+'-tool-check.json'))['version']=='cargo-kani 0.67.0','wrong Kani pin')
   log=(E/a/'stdout.log').read_text()
   require(('VERIFICATION:- SUCCESSFUL' if a==pos else 'VERIFICATION:- FAILED') in log,'wrong native result')
   if a==neg:require('** 1 of ' in log and 'assert_failed_inner' in log,'control failed outside assertion')
  require(obj(E/(pos+'-tool-check.json'))['binaries']==obj(E/(neg+'-tool-check.json'))['binaries'],'tool changed between controls')
 p=obj(E/'NEI_N006/receipt.json');n=obj(E/'NEI_N007/receipt.json')
 require([p['exit_status'],n['exit_status']]==[0,101] and p['source_hashes']==n['source_hashes'],'row differential/control verdict')
 env=copy.deepcopy(n['env']);require(env.pop('NEI_WRONG',None)=='1' and env==p['env'],'row fixture control configuration')
 require('emitted_model_cases=24' in (E/'NEI_N006/stdout.log').read_text(),'row fixtures not reached')
 require('shared row 0' in (E/'NEI_N007/stdout.log').read_text(),'row fixture control did not reach assertion')
 # Re-evaluate the existing fixture values under this run's pinned library.
 coherent=(E/'NEI_L037/stdout.log').read_text();legacy=(old/'NEG_L033/stdout.log').read_text()
 def values(s):
  m=re.search(r'Aeneas.Std.Result.ok\s*\[',s);require(m is not None,'missing row fixture output');i=s.index('[',m.start());start=i;depth=0
  while True:
   depth+=(s[i]=='[')-(s[i]==']');i+=1
   if depth==0:return json.loads(s[start:i])
 require(obj(E/'NEI_L037/receipt.json')['exit_status']==0 and values(coherent)==values(legacy),'row coherent fixture values changed')
 require(sha(R/packet['review']['path'])==packet['review']['sha256'],'row review drift')
 require(packet['remaining_inner_hypotheses']==[],'row inner result assumption')
 return dict(function=packet['function'],status='CLOSED-CONDITIONAL',route=packet['route'],composed_rows_closed=[],kani_credit=2)
