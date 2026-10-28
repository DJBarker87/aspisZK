"""Generate the original ExternalFuns update and every other-field frame.
The callback argument stays explicit until the complete emitted root is compiled.
This generic installation is not a completed V244 source/value law.
"""
from pathlib import Path
import re
D=Path('evidence/pv-b3p6-20261028/lean');src=Path('evidence/pv-b3p6-20261028/resolved/R1Z/ProverRwFullExternalFuns.lean').read_text();ids=list(map(int,re.findall(r'^  op(\d+)\b',src,re.M)));assert ids==list(range(262))
out=['''import PV_B3P_Carrier227
namespace PV_B3P_Install227
open Aeneas Aeneas.Std ProverRwFull
set_option autoImplicit false
abbrev Types := PV_B3P_Carrier227.Types
abbrev SourceQ := PV_B3P_227.aspis_core.field.QM31
abbrev SourceError := PV_B3P_227.aspis_core.state_only_prefix.r0.Error
abbrev Terminal := PV_B3P_227.reference_terminal.SemanticPublic →
  Array (Array SourceQ 29#usize) 3#usize → Array SourceQ 10#usize →
  PV_B3P_227.aspis_core.state_only_prefix.r0.Challenges →
  Result (core.result.Result SourceQ SourceError)

def transport (r : Result (core.result.Result SourceQ SourceError)) :
    Result (core.result.Result ProverRwFull.aspis_core.field.QM31 SourceError) :=
  match r with
  | .ok (.Ok value) => .ok (.Ok (PV_B3P_Carrier227.fromQ value))
  | .ok (.Err e) => .ok (.Err e)
  | .fail e => .fail e
  | .div => .div

@[reducible] def selected (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) : @ExternalFuns (Types base) :=
  letI : ExternalTypes := Types base
  {ops with op227 := fun p claims point c => transport (terminal
    (PV_B3P_Carrier227.semantic base p)
    (PV_B3P_Carrier227.mapArray (PV_B3P_Carrier227.mapArray PV_B3P_Carrier227.toQ) claims)
    (PV_B3P_Carrier227.mapArray PV_B3P_Carrier227.toQ point)
    (PV_B3P_Carrier227.challenges c))}

theorem source (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal)
    (p : @aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public (Types base))
    (claims : Array (Array aspis_core.field.QM31 29#usize) 3#usize)
    (point : Array aspis_core.field.QM31 10#usize)
    (c : aspis_core.state_only_prefix.r0.Challenges) :
    @ExternalFuns.op227 (Types base) (selected base ops terminal) p claims point c =
      transport (terminal (PV_B3P_Carrier227.semantic base p)
        (PV_B3P_Carrier227.mapArray (PV_B3P_Carrier227.mapArray PV_B3P_Carrier227.toQ) claims)
        (PV_B3P_Carrier227.mapArray PV_B3P_Carrier227.toQ point)
        (PV_B3P_Carrier227.challenges c)) := rfl

theorem error_tag (e : SourceError) : transport (.ok (.Err e)) = .ok (.Err e) := rfl
theorem fail_tag (e : Aeneas.Std.Error) : transport (.fail e) = .fail e := rfl
theorem div_tag : transport .div = .div := rfl

#print axioms source
#print axioms error_tag
#print axioms fail_tag
#print axioms div_tag
''']
for i in ids:
 if i==227:continue
 out.append(f'''theorem preserved_op{i} (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op{i} (Types base) (selected base ops terminal) =
      @ExternalFuns.op{i} (Types base) ops := rfl
#print axioms preserved_op{i}
''')
out.append('end PV_B3P_Install227\n');(D/'PV_B3P_Install227.lean').write_text('\n'.join(out))
