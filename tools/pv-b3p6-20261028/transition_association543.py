"""Bind exact Kani input/return adapters and fresh reference extraction.
Script-checked structural argument, not a Kani or Rust-semantics axiom.
"""
from pathlib import Path
import json,hashlib,re,sys
D=Path('evidence/pv-b3p6-20261028');R=D/'resume18';P=Path('tools/pv-b3p6-20261028/v244');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
ns={};exec(compile(Path('tools/pv-b3p6-20261028/std_resolve_d540.py').read_text().split('indices={}')[0],'<parser>','exec'),ns)
tokens,index=ns['tokens'],ns['index']
def defs(s):
 out={}
 for b in re.split(r'(?=^/-- \[)',s,flags=re.M):
  m=re.search(r'^(?:def|structure|inductive) (\S+)',b,re.M)
  if m:out[m[1]]=b[m.start():].split('\nend ')[0].split('\n#print')[0].strip()
 return out
fresh=R/'reference-terminal/generated';source=(fresh/'Funs.lean').read_text();old={};origin={}
for q in sorted((D/'lean').glob('PV_B3P_P227_*.lean'))+sorted((D/'lean').glob('PV_B3P_E227_*.lean')):
 for n,b in defs(q.read_text()).items():
  if n not in old:old[n]=b;origin[n]=q
rows=[]
for n,b in defs(source).items():
 assert n in old,n
 before=b
 # Existing API ports only; the shift's modulo-64 value is proved by
 # PV_B3P_ShiftPorts227.usize_u32_mod64, including arbitrary usize values.
 b=b.replace('Std.U64.wrapping_shr index level_index','Std.U64.wrapping_shr index (UScalar.cast .U32 level_index)')
 # Proof arguments of fixed-size constructors are not executable source.
 def erase_proofs(s):return re.sub(r'\s*\(by simp only \[List.length_cons,\s*List.length_nil\]; rfl\)','',s)
 assert re.sub(r'\s+',' ',erase_proofs(b))==re.sub(r'\s+',' ',erase_proofs(old[n])),n
 rows.append(dict(declaration=n,raw_sha256=hashlib.sha256(before.encode()).hexdigest(),retained_module=str(origin[n]),retained_module_sha256=sha(origin[n]),comparison='exact declaration text modulo whitespace and explicit array-length proof arguments',shift_port='usize_u32_mod64'if b!=before else None))
types=defs((fresh/'Types.lean').read_text());retained={}
for q in [D/'lean/PV_B3P_CompleteTypes227.lean',D/'lean/PV_B3P_SelectEmission227.lean']:
 if q.exists():retained.update(defs(q.read_text()))
for n,b in types.items():
 if n not in retained:
  matches=[]
  for q in (D/'lean').glob('PV_B3P_*Types227.lean'):
   if n in defs(q.read_text()):matches.append((q,defs(q.read_text())[n]))
  assert matches,n
  retained[n]=matches[0][1]
 # Old metadata can carry explicit discriminant information; constructor
 # names, order, payloads and all fields must remain identical.
 norm=lambda x:re.sub(r'\s+',' ',x.replace('discriminant isize, ','').replace('@[discriminant isize]\n',''))
 assert norm(b)==norm(retained[n]),n
for side,path in [('deployed',P/'host_terminal_kani16.rs'),('reference',P/'reference_terminal_kani16.rs')]:
 text=path.read_text();records=index(text)
 adapter=next(a for a in records if a['name']=='public' and 'crate::inputs16::Public16' in a['signature'])
 expected='''{SemanticPublic{variant:if p.variant {CompiledVariant::Withdrawal}else{CompiledVariant::PrivateTransfer},pool:p.pool,deployment_domain:p.domain,anchor:p.anchor,nullifier:p.nullifier,asset_id:p.asset,recipient:p.recipient,change:p.change,withdrawal_amount:p.amount,transition:p.transition}}'''
 assert tokens(adapter['body'])==tokens(expected)
 validate=next(a for a in records if a['name']=='validate' and 'crate::inputs16::Public16'in a['signature'])
 assert tokens(validate['body'])==tokens('{validate_transition(public(p)).map_err(|e|e as u8)}')
 raw=P/('reference_terminal.rs'if side=='reference'else 'host_terminal.rs');assert path.read_bytes().startswith(raw.read_bytes())
 if side=='reference':assert sha(raw)==json.loads((R/'reference-terminal/inputs.json').read_text())['sources'][str(raw)]
# Generator public() has no assume and creates independent symbolic values
# for every field, including all 320 digest words and both variant branches.
input_text=(P/'inputs16.rs').read_text();public=next(a for a in index(input_text)if a['name']=='public');digest=next(a for a in index(input_text)if a['name']=='digest')
assert 'assume'not in public['body']+digest['body']
assert tokens(digest['body'])==tokens('{let a:[u32;8]=kani::any();let mut d=[M31(0);8];let mut i=0;while i<8 {d[i]=M31(a[i]);i+=1;}d}')
for required in ['before[i]=digest();after[i]=digest();','while i<20','variant:kani::any()','pool:kani::any()','domain:kani::any()','recipient:if kani::any(){Some(digest())}else{None}','amount:kani::any()','asset:M31(kani::any())','change:digest()','anchor:digest()','nullifier:digest()']:
 assert tokens(required)==tokens(required) and required in public['body'],required
raw_target=defs(source)['reference_terminal.validate_transition'];code=raw_target.replace('def reference_terminal.validate_transition','def fresh_transition_reference543',1)
module='''import PV_B3P_P227_08
import PV_B3P_LinkDefinitions13227
import PV_B3P_TransitionAdapter543227
namespace PV_B3P_Association543227
open Aeneas Aeneas.Std PV_B3P_227 Result
set_option autoImplicit false
/-- Exact fresh ae1-2 target, with hash-checked same-origin callees reused.
Only the declaration name changes. No recurrence or constant is evaluated. -/
'''+code+'''

theorem transition_reference_equality543 :
    fresh_transition_reference543 = reference_terminal.validate_transition := by
  funext input
  rfl

theorem transition_reference_link543 :
    PV_B3P_Links13227.PV_B3P_Link_terminal_validate_transition fresh_transition_reference543 :=
  transition_reference_equality543

#print axioms transition_reference_equality543
#print axioms transition_reference_link543
end PV_B3P_Association543227
'''
p=D/'lean/PV_B3P_TransitionReference543227.lean'
if '--check'in sys.argv:assert p.read_text()==module
else:p.write_text(module)
report=dict(route="Kani equivalence (P6) with std parity by token identity plus structural per-item arguments (k''')",input_adapter='PublicInput543 / public_from_input543; field-for-field checks; both sides byte-prefix frozen source; all symbolic fields independent, no assumptions',input_roundtrips=['public_input_roundtrip543','input_public_roundtrip543'],return_adapter='exact map_err of two unit error variants to distinct u8 tags; inverse is proved for both errors and all source-Result constructors',return_lemmas=['error_tag_injective543','outcome_roundtrip543','observation_roundtrip543','observation_injective543','transition_adapter_transfer543'],reference_replay=dict(scope='N79160',inputs_sha256=sha(R/'reference-terminal/inputs.json'),outputs_sha256=sha(R/'reference-terminal/outputs.json'),functions=rows,types_same_origin_same_features=list(types),new_ordinary_external_holes=[],exact_target_sha256=hashlib.sha256(raw_target.encode()).hexdigest()),kani=dict(run='K72135',receipt='resume16/receipts/K72135/receipt/receipt.json',k3='K3-AUDIT-D537: exact selected source/symbols NOT EXPOSED; no suspended pass used',std="STD-STRUCTURAL-D542 transition group: all ordinary differences argued; compiler generated items V370; historical run reused, not repeated"),source_steps=[dict(source='Copy SemanticPublic and its two public transition records',model='same field projections of exact fresh target; shared inputs immutable; no allocation or identity-sensitive operation'),dict(source='pool/domain comparisons, sequence check, capacity, checked_add',model='exact extracted short-circuit nested binds; no check skipped or reordered; checked_next227 declaration matches replay; Option-none returns invalid-append'),dict(source='carry and levels 0..20, including continue and early Err',model='K72135 full-domain exact shipped/ref gate, source-bound fresh while emission; original Range source reduction differs only by proved reference transfer, no native model inferred from shape'),dict(source='frontier/empty-root compare, final Ok or invalid-append',model='exact fresh emitted loop/body/helper, same-origin constants and M31 eq checked; digest227 owned read copied from shared array without mutation'),dict(source='map_err(|e| e as u8) in harness',model='observation_roundtrip543 prevents any hidden error or panic collapse; public_input_roundtrip543 proves adapter covers all SemanticPublic')],domain='all representable SemanticPublic; no canonicality, valid-transition or honest-input premise',coverage_status='eligible after fresh TransitionReference543227 compile and final axioms audit; do not count a pending theorem',retained='Whole std panic/format observation and dependency cone, D188/matrix and concrete callback remain open; V370 / D381,D386 retained. No endpoint premise or T changes.')
(R/'TRANSITION-SOURCE-D543.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(dict(reference_functions=len(rows),same_origin_types=len(types),exact_adapters=2,generated=str(p))))
