"""Additional push gates; no original NEB check is removed or bypassed."""
import json,hashlib,re,copy,subprocess
obj=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def audit(E,R,packet,neb,require,function):
 require(packet['status']=='CLOSED-CONDITIONAL' and packet['route']=='D188_ACTUAL_BODY_ROW_BORROW_COMPOSITION','wrong push route')
 F='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
 require(packet['frozen_revision']==F and packet['child_packet']=='NEI_ROW_PACKET.json' and packet['suspended_neb_credits_restored']==[],'push child/frozen/credit drift')
 for item in packet['lean_evidence']:
  for theorem in item['theorems']:neb.check_receipt(item,theorem)
  d=obj(R/item['receipt'])
  for path,h in d['source_hashes'].items():require(sha(E/path.removeprefix('NEI_generated/'))==h,'push successful proof source drift')
 old=E.parent/'slice-q-mul-20261029'
 for n in ['Types.lean','Funs.lean']:
  require((E/'NEI_PushRaw'/n).read_text().replace('NEI_PushRaw','NEG_PushActual')==(old/'NEG_extracted/NEG_PushActual'/n).read_text(),'raw push output differs beyond namespace')
 require((old/'NEG_PushActual/Funs.lean').read_bytes()==(old/'NEG_extracted/NEG_PushActual/Funs.lean').read_bytes(),'inherited push body was edited')
 require((old/'NEG_PushActual/Types.lean').read_bytes()==(old/'NEG_L046/sources/NEG_generated/NEG_PushActual/Types.lean').read_bytes(),'inherited carrier alias changed')
 require('index_mut_back a1' in (old/'NEG_PushActual/Funs.lean').read_text(),'dropped Vec borrow restoration')
 source=subprocess.check_output(['git','show',F+':crates/aspis-r1-cost-probe/src/verifier.rs'],cwd=R).decode();native=(E/'NEI_push_native.rs').read_text()
 for n in ['push','update_residue_row','residue_limb_at','power_limb_at']:require(function(source,n)==function(native,n),'changed frozen push/child body')
 body=function(source,'push');require(hashlib.sha256(body[body.index('{'):].encode()).hexdigest()==packet['source_body_sha256'],'push body pin')
 for pos,neg,cfg,assertion in [('NEI_K015','NEI_K016','NEI_wrong_row_geometry','assert_failed_inner'),('NEI_K019','NEI_K020','NEI_wrong_disjoint','assertion failed: if cfg!(NEI_wrong_disjoint)')]:
  ds=[obj(E/a/'receipt.json') for a in [pos,neg]];require([d['exit_status'] for d in ds]==[0,1],'push native/control verdict')
  require(ds[0]['source_hashes']==ds[1]['source_hashes'] and ds[0]['native_command']==ds[1]['native_command'],'push native/control source drift')
  env=copy.deepcopy(ds[0]['env']);env['RUSTFLAGS']+=' --cfg '+cfg;require(env==ds[1]['env'],'push native/control cfg drift')
  for a,d in zip([pos,neg],ds):
   require(d['swaps']=='0' and d['limits']==dict(zip(['memory.high','memory.max','memory.swap.max','pids.max'],['6442450944','8589934592','0','64'])),'push caps/swap')
   require(d['copy_patch_sha256']=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67','push KMX pin')
   for n,h in d['source_hashes'].items():require(sha(E/a/'sources'/n)==h,'push archived native source')
   require(obj(E/(a+'-graph-check.json'))['graph_matches_frozen'] and obj(E/(a+'-lock-check.json'))['unchanged'],'push graph/lock drift')
   require(obj(E/(a+'-frozen-source-check.json'))['passed'] and obj(E/(a+'-rule16-check.json'))['static_declarations']==[],'push frozen/rule16 drift')
   require(obj(E/(a+'-tool-check.json'))['version']=='cargo-kani 0.67.0','push tool drift')
   log=(E/a/'stdout.log').read_text();require(('VERIFICATION:- SUCCESSFUL' if a==pos else 'VERIFICATION:- FAILED') in log,'push result mismatch')
   if a==neg:require('** 1 of ' in log and assertion in log,'push control failed outside intended assertion')
  require(obj(E/(pos+'-tool-check.json'))['binaries']==obj(E/(neg+'-tool-check.json'))['binaries'],'push pair binary drift')
 p=obj(E/'NEI_N008/receipt.json');n=obj(E/'NEI_N009/receipt.json')
 require([p['exit_status'],n['exit_status']]==[0,101] and p['source_hashes']==n['source_hashes'],'push differential/control verdict')
 env=copy.deepcopy(n['env']);require(env.pop('NEI_WRONG',None)=='1' and env==p['env'],'push fixture cfg mismatch')
 require('1 passed; 0 failed' in (E/'NEI_N008/stdout.log').read_text() and "thread 'NEI_push_differential'" in (E/'NEI_N009/stdout.log').read_text(),'push fixtures not reached')
 for a in ['NEI_N008','NEI_N009']:
  pins=obj(E/a/'NEI_NATIVE_PINS.json');require(pins['lock_before']==pins['lock_after']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef','native push lock drift')
  require(sorted(pins['features'].values(),key=len)==[[],['r0']],'native push feature drift')
  for path,h in pins['source_pins'].items():require(hashlib.sha256(subprocess.check_output(['git','show',F+':'+path],cwd=R)).hexdigest()==h,'native push core drift')
 def values(s):
  out=[]
  for m in re.finditer(r'Aeneas.Std.Result.ok\s*\[',s):
   i=s.index('[',m.start());start=i;depth=0
   while True:
    depth+=(s[i]=='[')-(s[i]==']');i+=1
    if depth==0:break
   out.append(json.loads(s[start:i]))
  return out
 current=values((E/'NEI_L048/stdout.log').read_text());legacy=values((old/'NEG_L054/stdout.log').read_text())
 expected=[0]*256+[3];expected[23*4:24*4]=[5,10,15,20]
 require(obj(E/'NEI_L048/receipt.json')['exit_status']==0 and current==[legacy[1],expected],'push coherent model fixtures drift')
 require(sha(R/packet['review']['path'])==packet['review']['sha256'] and packet['remaining_inner_hypotheses']==[],'push review/inner hypothesis')
 return dict(function=packet['function'],status='CLOSED-CONDITIONAL',route=packet['route'],composed_rows_closed=[],kani_credit=2)
