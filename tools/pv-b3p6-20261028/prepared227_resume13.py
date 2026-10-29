"""Compose source Range loops, exact accumulator steps and empty closure Drop.
This adds new explicit source models; immutable extraction files stay untouched.
"""
from pathlib import Path
D=Path('evidence/pv-b3p6-20261028');L=D/'lean'
base='''import PV_B3P_RangeBinding13227
import PV_B3P_ClosureDrop13227
import PV_B3P_LinkDefinitions13227
namespace PV_B3P_Binding13227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227 PV_B3P_Binding10227 PV_B3P_Binding12227 Result
set_option autoImplicit false
'''
s=base+'''
def source_component13 (left right : Channels12) (component : Usize) (sums : Matrix3x3) : Result Matrix3x3 :=
  range_loop13 (source_channel12 left right component) 0#usize 3#usize sums

theorem source_component_binding13 (left right : Channels12) (component : Usize) (sums : Matrix3x3) :
    source_component13 left right component sums = source_component12 left right component sums :=
  range_loop_binding13 _ _ _ _

def source_nested13 (left right : Channels12) (sums : Matrix3x3) : Result Matrix3x3 :=
  range_loop13 (fun sums component => source_component13 left right component sums) 0#usize 3#usize sums

theorem source_nested_binding13 (left right : Channels12) (sums : Matrix3x3) :
    source_nested13 left right sums = source_nested12 left right sums := by
  unfold source_nested13
  rw [range_loop_binding13]
  have steps : (fun sums component => source_component13 left right component sums) =
      (fun sums component => source_component12 left right component sums) := by
    funext sums component
    exact source_component_binding13 left right component sums
  rw [steps]
  rfl
'''
for name,p in [('source_accumulate12','PV_B3P_PreparedAccumulate12227'),('source_product_term12','PV_B3P_PreparedRoot12227'),('source_channel_reconstruct12','PV_B3P_PreparedRoot12227')]:
 raw=(L/(p+'.lean')).read_text();a=raw.index('def '+name+' ');end=raw.find('\ndef ',a+1);end2=raw.find('\nattribute ',a+1)
 b=min(x for x in [end,end2,len(raw)]if x>=0)
 decl=raw[a:b].rstrip();assert '\ntheorem 'not in decl
 decl=decl.replace(name,name.replace('12','13')).replace('source_nested12','source_nested13').replace('source_accumulate12','source_accumulate13').replace('reference_field.reconstruct_component','reconstruct_call_once13')
 s+='\n'+decl+'\n'
s+='''
attribute [local irreducible] aspis_core.field.CM31.add aspis_core.field.M31.add
  reference_field.reconstruct_component reference_field.cm31_mul_r
  aspis_core.field.CM31.sub Array.index_usize

theorem source_accumulate_binding13 (sums : Matrix3x3) (right : aspis_core.field.QM31)
    (left : reference_field.PreparedQm31Multiplier) :
    source_accumulate13 sums right left = source_accumulate12 sums right left := by
  unfold source_accumulate13 source_accumulate12
  simp only [source_nested_binding13]

theorem source_product_term_binding13 (left : Array reference_field.PreparedQm31Multiplier 3#usize)
    (right : Array aspis_core.field.QM31 3#usize) (sums : Matrix3x3) (index : Usize) :
    source_product_term13 left right sums index = source_product_term12 left right sums index := by
  unfold source_product_term13 source_product_term12
  simp only [source_accumulate_binding13]

theorem source_channel_reconstruct_binding13 (sums : Matrix3x3) :
    source_channel_reconstruct13 sums = source_channel_reconstruct12 sums := by
  unfold source_channel_reconstruct13 source_channel_reconstruct12
  simp only [reconstruct_call_once_binding13]

def source_prepared13 (left : Array reference_field.PreparedQm31Multiplier 3#usize)
    (right : Array aspis_core.field.QM31 3#usize) : Result aspis_core.field.QM31 := do
  let initial := Array.repeat 3#usize (Array.repeat 3#usize 0#u64)
  let sums ← range_loop13 (source_product_term13 left right) 0#usize 3#usize initial
  source_channel_reconstruct13 sums

theorem source_prepared_binding13 (left : Array reference_field.PreparedQm31Multiplier 3#usize)
    (right : Array aspis_core.field.QM31 3#usize) :
    source_prepared13 left right = reference_field.qm31_sum_products3_prepared left right := by
  rw [prepared_root_binding12]
  unfold source_prepared13 source_prepared12
  dsimp only
  rw [range_loop_binding13]
  have steps : source_product_term13 left right = source_product_term12 left right := by
    funext sums index
    exact source_product_term_binding13 left right sums index
  simp only [steps,source_channel_reconstruct_binding13]

theorem prepared_link13 :
    PV_B3P_Links13227.PV_B3P_Link_field_qm31_sum_products3_prepared source_prepared13 :=
  funext (fun left => funext (source_prepared_binding13 left))
#print axioms source_component_binding13
#print axioms source_nested_binding13
#print axioms source_accumulate_binding13
#print axioms source_product_term_binding13
#print axioms source_channel_reconstruct_binding13
#print axioms source_prepared_binding13
#print axioms prepared_link13
end PV_B3P_Binding13227
'''
(L/'PV_B3P_PreparedBinding13227.lean').write_text(s)
