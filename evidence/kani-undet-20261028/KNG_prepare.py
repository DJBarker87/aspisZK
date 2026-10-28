from pathlib import Path
import json,re,hashlib,subprocess
E=Path(__file__).resolve().parent;P=E.parent
sha=lambda b:hashlib.sha256(b).hexdigest()
# Complete additions in the packet are recipes, not claimed historical snapshots.
patch=(P/'native-tx2d-20261027/NBH_harness.patch').read_text();mods={}
for name in ['NBH_after','NBH_live']:
 tail=patch.split('+++ b/crates/aspis-statement/src/pool_v1/'+name+'.rs\n',1)[1].split('--- ',1)[0]
 mods['KNG_'+name]=''.join(line[1:]+'\n' for line in tail.splitlines() if line.startswith('+'))
for name in ['NBU_more','NBU_decode']:
 mods['KNG_'+name]=(P/'native-tx2j-20261028'/f'{name}.rs.txt').read_text()
mods['KNG_LPi_contracts']=(P/'kani-mitig-20261028/KMX_LPi_contracts.rs.txt').read_text()
# Exact published KMX implementation; unchanged complete file.
p=(P/'kani-mitig-20261028/KMX_copy_stubs.patch').read_text();tail=p.split('+++ b/KMX_stubs.rs\n',1)[1].split('diff --git',1)[0]
stubs=''.join(l[1:]+'\n' for l in tail.splitlines() if l.startswith('+'))
assert sha(stubs.encode())=='ad8efb63d8ff791274c91eff9ccc5b9fb126f5a3ac7f27aa811ca11b8e25c138'
(E/'KNG_KMX_stubs.rs.txt').write_text(stubs)
attrs='\n'.join('#[kani::stub('+a+',crate::KMX_stubs::'+b+')]' for a,b in [('<[u8]>::copy_from_slice','KMX_copy_from_slice'),('core::ptr::copy_nonoverlapping','KMX_copy_nonoverlapping'),('<[u8]>::clone_from_slice','KMX_clone_from_slice'),('alloc::vec::Vec::<u8>::extend_from_slice','KMX_extend_from_slice'),('<[u8]>::to_vec','KMX_to_vec'),('alloc::alloc::realloc','KMX_realloc')])
# Add matched controls to NBH: same domain/call, invert first equality only.
for name in ['KNG_NBH_after','KNG_NBH_live']:
 s=mods[name];controls=[]
 for mt in re.finditer(r'fn (NBH_(?:after_step|live_step|after_prefix_gate|live_prefix_gate|exact8|exact32))\(\)\s*\{',s):
  a=s.rfind('#[kani::proof]',0,mt.start());start=s.index('{',mt.start());depth=1;j=start+1
  while depth:depth+=(s[j]=='{')-(s[j]=='}');j+=1
  b=s[a:j];assert 'assert_eq!' in b
  controls.append(b.replace(mt[1]+'()',mt[1]+'_negative()',1).replace('assert_eq!','assert_ne!',1))
 s+='\n'+'\n'.join(controls)
 s=s.replace('#[kani::proof]','#[kani::proof]\n#[kani::unwind(70)]\n'+attrs)
 mods[name]=s
# KMX controls keep all observations, invert the payload equality only.
s=mods['KNG_LPi_contracts'];start=s.index('fn check_q<');end=s.index('fn check_c<')
q=s[start:end];q=q.replace('check_q','KNG_check_q_negative').replace('macro_rules! qcase','macro_rules! KNG_qcase_negative').replace('qcase!','KNG_qcase_negative!').replace('assert_eq!(buf[j],(x[k/4]','assert_ne!(buf[j],(x[k/4]')
for n in ['q_owned16','q_parent32_left','q_parent32_right','q_parent32_middle','q_parent48_middle','q_parent48_right']:
 q=q.replace('!('+n+',','!('+n+'_negative,')
mods['KNG_LPi_contracts']=s+'\n'+q
for name,text in mods.items():(E/(name+'.rs.txt')).write_text(text)
plan=[]
for row in json.loads((E/'KNG_INVENTORY.json').read_text()):
 old=row['harness'];a=row['historical_attempt'];prefix=a[:3]
 if prefix=='KMX':new=old.replace('KMX_LPi_contracts','KNG_LPi_contracts')
 elif prefix=='NBH':new=old.replace('::NBH_after::','::KNG_NBH_after::').replace('::NBH_live::','::KNG_NBH_live::')
 else:new=old.replace('::NBU_more::','::KNG_NBU_more::').replace('::NBU_decode::','::KNG_NBU_decode::')
 plan.append(dict(historical_attempt=a,positive=new,control=new+'_negative',crate='aspis-r1-cost-probe' if prefix=='KMX' else 'aspis-statement',reconstruction='Packet complete recipe; historical whole-file hash differs. Same recorded property/domain and child cuts; no claim of historical byte identity.',rule14=False))
(E/'KNG_RUN_PLAN.json').write_text(json.dumps(plan,indent=2)+'\n')
(E/'KNG_RECONSTRUCTION_HASHES.json').write_text(json.dumps({p.name:sha(p.read_bytes()) for p in sorted(E.glob('*.rs.txt'))},indent=2)+'\n')
