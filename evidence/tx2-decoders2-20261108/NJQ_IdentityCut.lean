import NJQ_Identity
import NJI_PolicyCut
set_option autoImplicit false
noncomputable section
namespace NJQ_IdentityCut
open Aeneas Aeneas.Std Result NJQ_Identity
attribute [local instance] Classical.propDecidable

def prefixError (b : Slice U8) (len : b.val.length=144) : Option NJQ_Identity.Error :=
 if b.val.take 4≠magic.val then some .WrongMagic else
 if NHY_ZeroStep.byte b 4≠1#u8 then some .WrongVersion else
 if (b.val.drop 5).take 3≠List.replicate 3 0#u8 ∨ (b.val.drop 108).take 4≠List.replicate 4 0#u8 then some .NonZeroReserved else
 if (record b len).asset_id<2147483647#u32 then none else some .NonCanonicalAssetId

def Coordinates (b : Slice U8) (len : b.val.length=144) (p : Identity) : Prop :=
 p.asset_id=(record b len).asset_id ∧ ∀ i,i<32 →
 NHY_ArrayExt.coord p.pool i=NHY_ZeroStep.byte b (8+i) ∧
 NHY_ArrayExt.coord p.asset_mint i=NHY_ZeroStep.byte b (40+i) ∧
 NHY_ArrayExt.coord p.token_program i=NHY_ZeroStep.byte b (72+i) ∧
 NHY_ArrayExt.coord p.deployment_domain i=NHY_ZeroStep.byte b (112+i)

theorem complete_record (b : Slice U8) (len : b.val.length=144) (p : Identity)
 (h : Coordinates b len p) : p=record b len := by
 have pool : p.pool=(record b len).pool := by
  apply NHY_ArrayExt.whole
  intro i hi _
  rw [show (record b len).pool=NHY_NaturalReads.array b 8 32#usize (by change 8+32≤b.val.length;omega) from rfl]
  rw [NJI_PolicyCut.field_coordinate b 8 i _ hi]
  exact (h.2 i hi).1
 have mint : p.asset_mint=(record b len).asset_mint := by
  apply NHY_ArrayExt.whole
  intro i hi _
  rw [show (record b len).asset_mint=NHY_NaturalReads.array b 40 32#usize (by change 40+32≤b.val.length;omega) from rfl]
  rw [NJI_PolicyCut.field_coordinate b 40 i _ hi]
  exact (h.2 i hi).2.1
 have token : p.token_program=(record b len).token_program := by
  apply NHY_ArrayExt.whole
  intro i hi _
  rw [show (record b len).token_program=NHY_NaturalReads.array b 72 32#usize (by change 72+32≤b.val.length;omega) from rfl]
  rw [NJI_PolicyCut.field_coordinate b 72 i _ hi]
  exact (h.2 i hi).2.2.1
 have domain : p.deployment_domain=(record b len).deployment_domain := by
  apply NHY_ArrayExt.whole
  intro i hi _
  rw [show (record b len).deployment_domain=NHY_NaturalReads.array b 112 32#usize (by change 112+32≤b.val.length;omega) from rfl]
  rw [NJI_PolicyCut.field_coordinate b 112 i _ hi]
  exact (h.2 i hi).2.2.2
 have asset:=h.1
 cases p
 unfold record at *
 simp_all

def Cut (b : Slice U8) (out : core.result.Result Identity NJQ_Identity.Error) : Prop :=
 if len : b.val.length=144 then
  match prefixError b len with
  | some e=>out=.Err e
  | none=>∃p,out=.Ok p ∧ Coordinates b len p
 else out=.Err .WrongLength

theorem native_source (b : Slice U8) (out : core.result.Result Identity NJQ_Identity.Error) (cut : Cut b out) :
 ok out=reference b := by
 rw [source]
 unfold Cut at cut
 unfold model
 split at cut
 · rename_i len
   simp only [dif_pos len]
   by_cases hm : b.val.take 4=magic.val <;>
    by_cases hv : NHY_ZeroStep.byte b 4=1#u8 <;>
    by_cases h1 : (b.val.drop 5).take 3=List.replicate 3 0#u8 <;>
    by_cases h2 : (b.val.drop 108).take 4=List.replicate 4 0#u8 <;>
    by_cases ha : (record b len).asset_id<2147483647#u32 <;>
     simp_all [prefixError]
   all_goals first
    | exact congrArg Result.ok cut
    | (obtain ⟨p,ret,coords⟩:=cut
       rw [complete_record b len p coords] at ret
       first | exact ret | exact congrArg Result.ok ret)
 · rename_i wrong
   simp only [dif_neg wrong]
   exact congrArg Result.ok cut

set_option pp.proofs false in
#print native_source
#print axioms complete_record
#print axioms native_source
end NJQ_IdentityCut
