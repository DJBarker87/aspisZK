import NKR_TermDigestCut
import NJX_DigestGroups
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKR_TermDigestFrame
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K)
open FIw_ArrayValue (decoded)
def packed (old : Array NQ 8#usize) (g : Fin 2) : K :=
 NJB_PackLinearity.pack (fun j=>decoded old (NJX_DigestGroups.index g j))
/-- Explicit packing-map identity avoids an unresolved pack-argument
metavariable forcing normalization of the concrete tower basis. -/
theorem pack_eq (v : Fin 4 → K) : FIx_PreweightedPack.pack v=NJB_PackLinearity.pack v := rfl

theorem selected_at (a : Fin 8 → K) (g : Fin 2) (lane : Fin 4) :
 FIx_SelectedMeaning.selected a 84 (21+g.val) lane.val=a (NJX_DigestGroups.index g lane) := by
 unfold FIx_SelectedMeaning.selected
 have hg:=g.isLt
 have hl:=lane.isLt
 rw [dif_pos (by constructor <;> omega)]
 apply congrArg a
 apply Fin.ext
 simp only [NJX_DigestGroups.index]
 omega

theorem selected_outside (a : Fin 8 → K) (j : Nat) (lane : Fin 4) (h21 : j≠21) (h22 : j≠22) :
 FIx_SelectedMeaning.selected a 84 j lane.val=0 := by
 unfold FIx_SelectedMeaning.selected
 have h:=lane.isLt
 rw [dif_neg (by omega)]

/-- Symbolic sparse footprint, replacing L142's unresolved-change shape.
The packing function stays opaque while its four selected inputs are proved. -/
theorem increment (old : Array NQ 8#usize) (j : Fin (24#usize).val) :
 FIx_SelectedMeaning.contribution (decoded old) 84 j.val=
 if j.val=21 then packed old 0 else if j.val=22 then packed old 1 else 0 := by
 by_cases h21 : j.val=21
 · rw [if_pos h21]
   unfold FIx_SelectedMeaning.contribution packed
   rw [pack_eq]
   apply congrArg NJB_PackLinearity.pack
   funext lane
   rw [h21]
   erw [selected_at (decoded old) 0 lane]
 · rw [if_neg h21]
   by_cases h22 : j.val=22
   · rw [if_pos h22]
     unfold FIx_SelectedMeaning.contribution packed
     rw [pack_eq]
     apply congrArg NJB_PackLinearity.pack
     funext lane
     rw [h22]
     erw [selected_at (decoded old) 1 lane]
   · rw [if_neg h22]
     unfold FIx_SelectedMeaning.contribution
     rw [pack_eq]
     have cells : (fun lane : Fin 4=>FIx_SelectedMeaning.selected (decoded old) 84 j.val lane.val)=fun _=>0 := by
      funext lane
      exact selected_outside (decoded old) j.val lane h21 h22
     erw [cells,NJB_PackLinearity.zero]
#print axioms pack_eq
#print axioms selected_at
#print axioms selected_outside
#print axioms increment
end AspisR1.NKR_TermDigestFrame
end
