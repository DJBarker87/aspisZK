import R1Z.PV_Src_PortJoinedWords
import R1Z.PV_Src_PortNodeTweak
set_option autoImplicit false
namespace R1Z.PV_Src_PortNodePreMeaning
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
variable {K : Type} [Field K]

def model (left right : Array U32 8#usize) (j : Fin 16) : K :=
  if j.val<8 then liftU left.val[j.val]!
  else if j.val=15 then liftU right.val[7]! - (1051521018 : K)
  else liftU right.val[j.val-8]!

theorem source (left right : Array U32 8#usize) (z : U32)
    (hz : liftU (K := K) z = liftU right.val[7]! - (1051521018 : K)) :
    liftA (K := K) ((PV_Src_PortNodeCopy.joined left right).set 15#usize z) = model left right := by
  funext j
  change liftU (((PV_Src_PortNodeCopy.joined left right).set 15#usize z).val[j.val]!) = _
  rw [set_get' _ 15#usize z (by decide) j.val,PV_Src_PortJoinedWords.source left right j]
  simp only [UScalar.ofNatCore_val_eq,model]
  by_cases h15 : j.val=15
  · have h8 : ¬ j.val<8 := by omega
    rw [if_pos h15,if_neg h8,if_pos h15]
    exact hz
  · rw [if_neg h15]
    by_cases h8 : j.val<8
    · rw [if_pos h8,if_pos h8]
    · rw [if_neg h8,if_neg h8,if_neg h15]

#print axioms source
end R1Z.PV_Src_PortNodePreMeaning
