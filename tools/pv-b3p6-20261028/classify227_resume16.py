"""Conservative per-function routing; never infer extraction acceptance from shape."""
from pathlib import Path
import re,json,hashlib,subprocess
D=Path('evidence/pv-b3p6-20261028');O=D/'resume16'
inv=json.loads((D/'resume9/body-inventory.json').read_text())
status=(D/'resume15/GROUP-STATUS.md').read_text()
rows=[]
control={'add_preweighted','sum_high','reconstruct_10','selector_mask_sum_16','validate_transition','external_linear_lazy','external_linear_packed','external_local_packed_raw','internal_linear_lazy','add_schedule_lanes','semantic_packed'}
for line in status.splitlines():
 if not line.startswith('| ') or '| **OPEN**' not in line:continue
 name=line.split('|')[1].strip();matches=[r for r in inv['bodies'] if r['key']==name+'#0' and r['status']=='changed']
 if name in ['at_point','expand']:matches=[r for r in inv['bodies'] if r['family']=='poseidon' and r['key']==name+'#0']
 if not matches:matches=[r for r in inv['bodies'] if r['key']==name+'#0']
 assert matches,name
 # Constructor at_point/expand identify terminal family when multiple owned entries exist.
 r=next((r for r in matches if r['family']=='terminal'),matches[0]);family=r['family']
 files={f['family']:f for f in inv['files']};f=files[family]
 src=r['source'];owned=r['owned'];sp=(src or {}).get('source_file',f['source'])
 if sp.startswith('tools/') and '/host_' in sp:sp='crates/aspis-r1-cost-probe/src/'+Path(sp).name
 # Source-only constructor remains a genuine domain/layout obligation.
 result=subprocess.run(['rg','-n',r'\b'+re.escape(name)+r'\s*(?:::<[^>]*>)?\s*\(','crates/'],capture_output=True,text=True)
 calls=result.stdout.splitlines()
 route='b' if name in control else 'c'
 narrowed={'selector_mask_sum_16':'mask in {1749,2048,2049,4097,6144,6145,26214}; caller active_literal tests mask != 0; frozen table checked separately', 'add_preweighted':'8 actual monomorphized (N,start) call shapes; positive N and start+N<=96', 'sum_high':'deployed caller arrays have at most 2 ranges; endpoints <=64; empty/reversed ranges included','qm31_m31_dot':'reference fixes length=7; all caller lengths and values must be checked','at_point':'reference terminal constructor uses 57 layout blocks; legacy 49 requires a separate link','expand':'N and coordinate range follow constructor; must retain frame and failure behavior'}.get(name,'no narrowed domain established; full caller domain remains required')
 rows.append(dict(function=name,family=family,route=route,route_label='control/index/small-width equivalence' if route=='b' else 'chained-field equivalence only modulo shared cited pure deterministic callees',deployed_source=sp,source_span=None if not src else [src['line'],src['end_line']],reference_source=f['owned'],reference_span=None if not owned else [owned['line'],owned['end_line']],model_context='AVAILABLE' in line,direct_extraction=dict(status='NOT ATTEMPTED: zero other-native-scope allocation; acceptance unknown',refusal_verbatim=None),domain=narrowed,callsite_grep=calls,callee_associations='OPEN; cannot stub separately defined host/reference callees as a shared callee',equivalence='PENDING',composed_binding='OPEN'))
assert len(rows)==36,len(rows)
record=dict(revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),scope='V244 36 groups from resume15; no pruning',routes_are_provisional=True,direct_extraction_scope_conflict='Fresh trials require Charon/Aeneas native scopes; prompt allocates 0 other native scopes. No refusal fabricated.',functions=rows,requested_ancillary=[dict(function='add_preweighted_shared_selector',reason='not in historical 36: cfg optimized-terminal; requested explicitly; ancillary gate retained without changing denominator'),dict(function='selector_mask_sum_16 (aspis-statement copy)',reason='separate deployed copy requested explicitly; token-identical body requires a separate evidence chain')])
(O/'CLASSIFY.json').write_text(json.dumps(record,indent=2)+'\n')
print('classified',len(rows),'routes',{k:sum(x['route']==k for x in rows)for k in ['a','b','c']})
