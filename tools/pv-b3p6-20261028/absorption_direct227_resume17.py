"""Instantiate the exact deployed extraction in the existing type/callee carrier.
Only imports/namespace and the explicit opaque RATE constant are adapted; raw
outputs are retained. Shared declarations must have identical Lean tokens.
"""
from pathlib import Path
import re,json,hashlib
D=Path('evidence/pv-b3p6-20261028');R=D/'resume17/raw/terminal-absorption';L=D/'lean'
raw=(R/'Funs.lean').read_text();old=(D/'raw227-composition-resume5/Funs.lean').read_text()
def decls(s):
 out={}
 for b in re.split(r'(?=^/-- \[)',s,flags=re.M):
  m=re.search(r'^(?:def|structure|inductive) (\S+)',b,re.M)
  if m:
   t=b[m.start():];t=re.split(r'^end PV_B3P_',t,flags=re.M)[0].strip();out[m[1]]=t
 return out
lex=lambda s:re.findall(r'\w+|[^\s]',s)
a,b=decls(raw),decls(old);shared=[];target=[]
for n,t in a.items():
 if n.startswith('host_terminal.absorption_lanes_literal'):target.append(t)
 else:
  assert n in b,n
  assert lex(t)==lex(b[n]),n
  shared.append(n)
oldtypes=decls((D/'raw227-composition-resume5/Types.lean').read_text())
for n,t in decls((R/'Types.lean').read_text()).items():assert lex(t)==lex(oldtypes[n]),n
assert len(target)==3
s='''import PV_B3P_AbsorptionSource15227
namespace PV_B3P_227
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false
'''
for t in target:s+='\n'+t.replace('aspis_statement.poseidon2.RATE','(Result.ok aspis_statement.poseidon2.RATE)')+'\n'
s+='''end PV_B3P_227
namespace PV_B3P_Direct17227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227 PV_B3P_Native15227 Result
set_option autoImplicit false
attribute [local irreducible] aspis_core.field.QM31.add aspis_core.field.QM31.mul Array.update

theorem absorption_body17 (low fixed two eight nodes : aspis_core.field.QM31)
    (opened output : Array aspis_core.field.QM31 16#usize) (lane : Usize) :
    host_terminal.absorption_lanes_literal_loop.body low fixed two eight nodes opened output lane =
      usize_body (absorption_source_step15 low fixed two eight nodes opened) 16#usize (output,lane) := by
  by_cases h : lane < 16#usize <;> by_cases h2 : lane < 2#usize <;>
    by_cases hrate : lane < aspis_statement.poseidon2.RATE <;>
    simp only [host_terminal.absorption_lanes_literal_loop.body,usize_body,
      absorption_source_step15,absorption_native_value15,h,h2,hrate,
      if_true,if_false,bind_tc_ok,PV_B3P_Ordered227.bind_assoc]

theorem absorption_loop17 (low fixed two eight nodes : aspis_core.field.QM31)
    (opened output : Array aspis_core.field.QM31 16#usize) (lane : Usize) :
    host_terminal.absorption_lanes_literal_loop low fixed two eight nodes opened output lane =
      loop (usize_body (absorption_source_step15 low fixed two eight nodes opened) 16#usize) (output,lane) := by
  unfold host_terminal.absorption_lanes_literal_loop
  have same : (fun (state : Array aspis_core.field.QM31 16#usize × Usize) =>
      host_terminal.absorption_lanes_literal_loop.body low fixed two eight nodes opened state.1 state.2) =
      usize_body (absorption_source_step15 low fixed two eight nodes opened) 16#usize := by
    funext state
    exact absorption_body17 low fixed two eight nodes opened state.1 state.2
  rw [same]

theorem absorption_extraction_reference17 (low fixed two eight nodes : aspis_core.field.QM31)
    (opened : Array aspis_core.field.QM31 16#usize) :
    host_terminal.absorption_lanes_literal low fixed two eight nodes opened =
      reference_terminal.absorption_lanes_literal low fixed two eight nodes opened := by
  apply Eq.trans _ (absorption_source_binding15 low fixed two eight nodes opened)
  unfold host_terminal.absorption_lanes_literal absorption_source15
  exact absorption_loop17 low fixed two eight nodes opened _ _
#print axioms absorption_body17
#print axioms absorption_loop17
#print axioms absorption_extraction_reference17
end PV_B3P_Direct17227
'''
(L/'PV_B3P_DirectAbsorption17227.lean').write_text(s)
(R.parent.parent/'absorption-port.json').write_text(json.dumps(dict(raw_sha256=hashlib.sha256(raw.encode()).hexdigest(),shared_declarations_identical_tokens=shared,types_identical_tokens=True,definition_count=3,opaque_instantiation={'aspis_statement.poseidon2.RATE':'Result.ok PV_B3P_227.aspis_statement.poseidon2.RATE','deployed_source':'crates/aspis-statement/src/poseidon2.rs:57','source_body':'pub const RATE: usize = 8;','existing_extraction':'PV_B3P_227.aspis_statement.poseidon2.RATE = 8#usize'},no_external_axiom_template_compiled=True,changes=['imports and namespace','explicit opaque constant parameter instantiated with its identical deployed/extracted literal'],evidence_class='reclassification within existing Charon/Aeneas tool trust (owner fifth amendment)'),indent=2)+'\n')
