"""Symbolic complete-Result factorization of the 23-chunk encoder."""
from pathlib import Path
D=Path('evidence/pv-b3p6-20261028/lean');ns='PV_B3P_EncodeLaw226'
s='''import PV_B3P_BytesV3Emission226
import PV_B3P_RustResult
namespace PV_B3P_EncodeLaw226
open Aeneas Aeneas.Std PV_B3P_226V3 PV_B3P_RustResult
set_option autoImplicit false
attribute [local irreducible] reference226.byte_at reference226.chunk8 reference226.chunk
abbrev E := aspis_core.state_only_prefix.r0.Error
def spec (p : reference226.OwnedPublic) :
    Result (core.result.Result ((Array (Array U8 64#usize) 23#usize) × Usize) E) :=
'''
for k in range(23):s+='  '*(k+1)+f'bindR (reference226.chunk p {64*k}#usize) (fun v{k} =>\n'
s+='  '*24+'.ok (.Ok (Array.make 23#usize ['+','.join(f'v{k}' for k in range(23))+'] (by rfl), if p.withdrawal then 1427#usize else 1455#usize))'+')'*23+'\n'
s+='''theorem update_eq (p : reference226.OwnedPublic) (b : Bool) (h : b = p.withdrawal) :
    {p with withdrawal := b} = p := by
  subst b
  cases p
  rfl
#print axioms update_eq
set_option backward.isDefEq.respectTransparency false in
theorem complete_result (p : reference226.OwnedPublic) :
    reference226.encode_owned p = spec p := by
  unfold reference226.encode_owned spec
  cases hw : p.withdrawal
  all_goals
    have hu := update_eq p _ hw.symm
    simp only [hw,Bool.false_eq_true,↓reduceIte,bind_tc_ok] 
    rw [hu]
'''
for k in range(23):
 indent='    '+' '*4*k
 s+=indent+f'generalize h{k} : reference226.chunk p {64*k}#usize = r{k}\n'
 s+=indent+f'cases r{k} with\n'+indent+'| fail e => rfl\n'+indent+'| div => rfl\n'+indent+'| ok v =>\n'+indent+'  cases v with\n'+indent+'  | Err e => rfl\n'+indent+f'  | Ok v{k} =>\n'
s+='    '+' '*92+'rfl\n#print axioms complete_result\nend '+ns+'\n'
(D/(ns+'.lean')).write_text(s)
