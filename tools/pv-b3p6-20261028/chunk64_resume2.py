"""Factor the 64-byte emission through eight checked eight-byte blocks."""
from pathlib import Path
D=Path('evidence/pv-b3p6-20261028/lean')
ns='PV_B3P_Chunk64Law226'
s='''import PV_B3P_BytesV3Emission226
import PV_B3P_RustResult
import PV_B3P_Repeat226
import PV_B3P_ArrayEight226
namespace PV_B3P_Chunk64Law226
open Aeneas Aeneas.Std PV_B3P_226V3 PV_B3P_RustResult
set_option autoImplicit false
attribute [local irreducible] reference226.byte_at reference226.chunk8 Array.index_usize
abbrev E := aspis_core.state_only_prefix.r0.Error
'''
s+='def join (xs : List (Array U8 8#usize)) (h : xs.length = 8) : Array U8 64#usize :=\n  Array.make 64#usize (xs.flatMap (fun x => x.val)) (by\n    have hh : ∀ ys : List (Array U8 8#usize), (ys.flatMap (fun x => x.val)).length = ys.length * 8 := by\n      intro ys\n      induction ys with\n      | nil => rfl\n      | cons y ys ih => simp only [List.flatMap_cons,List.length_append,y.property,List.length_cons,ih, show (8#usize).val = 8 from rfl]; omega\n    rw [hh,h]; rfl)\n'
s+='def spec (p : reference226.OwnedPublic) (base : Usize) : Result (core.result.Result (Array U8 64#usize) E) :=\n'
for k in range(8):s+='  '*(k+1)+f'bindR (reference226.chunk8 p (Usize.wrapping_add base {k*8}#usize)) (fun v{k} =>\n'
s+='  '*9+'.ok (.Ok (join ['+','.join(f'v{k}' for k in range(8))+'] (by rfl)))'+')'*8+'\n'
s+='''set_option backward.isDefEq.respectTransparency false in
theorem complete_result (p : reference226.OwnedPublic) (base : Usize) :
    reference226.chunk p base = spec p base := by
  unfold reference226.chunk spec
  conv_lhs => whnf
'''
for k in range(8):
 indent='  '+' '*4*k
 if k:s+=indent+'conv_lhs => whnf\n'
 s+=indent+f'generalize h{k} : reference226.chunk8 p (Usize.wrapping_add base {8*k}#usize) = r{k}\n'
 s+=indent+f'cases r{k} with\n'+indent+'| fail e => rfl\n'+indent+'| div => rfl\n'+indent+'| ok v =>\n'+indent+'  cases v with\n'+indent+'  | Err e => rfl\n'+indent+f'  | Ok v{k} =>\n'
# indentation branches are 4 each loop
indent='  '+' '*32
s+=indent+'conv_lhs => whnf\n'
for k in range(8):
 for j in range(8):s+=indent+f'rw [PV_B3P_Repeat226.index_value v{k} {j}#usize (by decide)]\n'+indent+'conv_lhs => whnf\n'
s+=indent+'apply congrArg (fun a => Result.ok (core.result.Result.Ok a))\n'+indent+'apply Subtype.ext\n'+indent+'change _ = (['+','.join(f'v{k}' for k in range(8))+'].flatMap (fun a => a.val))\n'+indent+'simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil,← PV_B3P_ArrayEight226.values]\n'+indent+'rfl\n'
s+='#print axioms complete_result\nend '+ns+'\n'
(D/(ns+'.lean')).write_text(s)
