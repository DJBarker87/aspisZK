"""Check all three fixed map constructors and the ordered internal pair."""
from pathlib import Path
import json,hashlib
D=Path('evidence/pv-b3p6-20261028');R=D/'resume18';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
ns={};exec(compile(Path('tools/pv-b3p6-20261028/std_resolve_d540.py').read_text().split('indices={}')[0],'<parser>','exec'),ns)
tokens,index=ns['tokens'],ns['index'];p=Path('crates/aspis-statement/src/state_only_poseidon.rs');q=Path('tools/pv-b3p6-20261028/v244/reference_poseidon.rs')
assert sha(p)==json.loads((D/'resume17/deployed-source-pins.json').read_text())[str(p)]
a=next(x for x in index(p.read_text())if x['name']=='interpolated_internal_pair')
expected='''{const ROWS:[usize;7]=[2,3,4,5,6,7,8];let weights=ROWS.map(|row|local[row]);let even_constants=ROWS.map(|row|M31(INTERNAL[2*(row-2)]));let odd_constants=ROWS.map(|row|M31(INTERNAL[2*(row-2)+1]));let even=qm31_m31_dot(&weights,&even_constants);let odd=qm31_m31_dot(&weights,&odd_constants);internal_round(internal_round(state,even),odd)}'''
assert tokens(a['body'])==tokens(expected)
reference=json.loads((R/'REFERENCE-PROJECTED-D547.json').read_text())
required=['reference_poseidon.interpolated_internal_pair','reference_field.qm31_m31_dot','reference_poseidon.internal_round','reference_poseidon.INTERNAL']
assert all(n in [d['declaration']for d in reference['declarations']]for n in required)
steps=[
 ('ROWS=[2,3,4,5,6,7,8]','rows_map550','Exactly seven ascending callback applications; map produces an owned seven-element result, no filtering or padding. Reuse core array map/try_map/Guard source argument in ARRAY-INTERFACE-D543 and STD-STRUCTURAL-D542: cursor advanced before callback, initialized prefix and unconsumed suffix handled on failure. Callbacks are bounded reads and total wrapping arithmetic, so their failure/drop paths are unreachable; Copy/FnMut/drop lowering remains V370.'),
 ('weights=ROWS.map(local[row])','rows_map550 (Array.index_usize local1)','Same seven local reads2..8 within16; no mutable alias or state change. Array holds raw QM31, no canonicality assumption.'),
 ('even_constants map2*(row-2)','rows_map550 even_row550','Same subtraction then multiplication; row2..8 yields offsets0,2,..12 all<14. The actual expression tree is retained, not constant-folded in the equality proof. M31 tuple constructor preserves the raw u32 from INTERNAL.'),
 ('odd_constants map2*(row-2)+1','rows_map550 odd_row550','Same subtraction, multiplication, addition, and bound1,3,..13<14. Independent map after all even cells; constants/feature origin checked by N79167 exact reference comparison.'),
 ('even dot then odd dot','internal_pair_source550 two named calls','Both dot calls receive exactly the ordered seven weights and seven constants, unchanged input wrapper shape. Dot7 caller bounds/partition remain a separate helper-body obligation until dot source association is supplied. No callee is replaced by a field identity or arithmetic abstraction.'),
 ('internal_round(internal_round(state,even),odd)','internal_pair_source550 suffix','Exactly two sequential calls, passing every element of the first returned array to the second. No intermediate state, write, error or callback is omitted.')]
x=dict(function='interpolated_internal_pair',source=dict(path=str(p),sha256=sha(p),item=a,whole_body_tokens_checked=True),interpreter='internal_pair_source550',theorem='PV_B3P_Association550227.internal_pair_source_link550',source_steps=[dict(source=s,model=m,argument=v)for s,m,v in steps],reference=dict(receipt='N79167',comparison='REFERENCE-PROJECTED-D547.json',comparison_sha256=sha(R/'REFERENCE-PROJECTED-D547.json'),complete_declarations=required),domain='all raw state[16] and local[16]; no canonicality restriction',D188='no source mutable borrow; map arrays owned, both round result arrays passed intact',feature_profile='deployed ct-host-prover/release; no cfg/cfg! in item; resolved graph recorded by N79167',route='own-1 structural argument + complete-Result Lean equality',retained='dot helper source association, whole std/D188/matrix/callback and V370/D381/D386',status='pending focused proof; no credit yet')
(R/'INTERNAL-PAIR-SOURCE-D550.json').write_text(json.dumps(x,indent=2)+'\n');print(json.dumps(dict(bodies=1,map_cells=21)))
