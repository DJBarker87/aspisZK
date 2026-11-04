"""One source operand projection from an unrestricted actual typed pre-state."""
from NFD_native_patch import E,frozen,program,helpers
import sys,subprocess,json,re
slot=int(sys.argv[1]);mode=sys.argv[2];assert 0<=slot<3 and mode in ['positive','negative']
subprocess.run([sys.executable,str(E/'NFD_prepare_window.py'),'1','positive'],check=True)
# Reuse the exact direct actual-type factory, never the timed-out overwrite factory.
s=(E/'NFD_prepare_reconstruct.py').read_text();factory=s[s.index("base=helpers();auth=''"):s.index('fields=[];all_fields=[]')]
exec(factory,globals())
fields=['a.live_snapshot.next_pair_index','a.master.identity.asset_id.0','c.next_pair_index'];ty=['u64','u32','u64'][slot]
expression=['authenticated.live_snapshot.next_pair_index','authenticated.master.identity.asset_id','candidate_afterstate.next_pair_index'][slot]
value=expression+('.0' if slot==1 else '')
code='let mut a=auth();let mut c=NEE_common().lane_transition.candidate_afterstate;let chosen:'+ty+'=kani::any();'+fields[slot]+'=chosen;let authenticated=&a;let candidate_afterstate=&c;let observed='+value+';assert!(observed==chosen'+('^1' if mode=='negative' else '')+');'
body=base+auth+attrs+'fn operand(){'+code+'}\n';program(body,'NFD_operand')
p='programs/r1-cost-probe/src/r1_pool_adapter.rs';f=frozen(p);a=f.index('fn reconstruct_asq8_statement(');original=f[a:f.index('\n}',a)+2];assert expression in original
(E/'NFD_OPERAND_CURRENT.json').write_text(json.dumps(dict(slot=slot,mode=mode,source=body,frozen_body=original,frozen_expression=expression,domain='all typed Auth/Candidate inputs; chosen scalar and every other cell independently arbitrary; observation indices absent',classification='one actual native source operand load, with a controlled arbitrary scalar in that field and matched corrupt-value control; all typed states represented, immutable source footprint'),indent=1)+'\n')
