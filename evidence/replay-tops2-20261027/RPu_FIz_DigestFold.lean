import RPu_FIz_DigestFrontier
import RPu_FIy_FrontierLoop
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIz_DigestFold
open Aeneas Aeneas.Std
open FIv_NativeValue (K)
open FIw_PublicModel (Public Openings Selectors)
theorem value (p : Public) (o : Openings) (s : Selectors) (n start : Nat) (bound : start+n≤20)
    (old : Fin 8 → K) :
    FIy_FrontierLoop.model p.transition.live_snapshot s o.z n start old=
      (List.ofFn (fun i : Fin n=>R0P.DigestKey.frontier ⟨start+i.val,by omega⟩)).foldl
        (fun acc key=>R0P.digestAddBinding acc
          (FIw_PublicModel.selector s (R0P.digestRow (FIw_PublicModel.ofPublic p) key))
          (FIw_PublicModel.openings o).z (R0P.digestStart (FIw_PublicModel.ofPublic p) key)
          (R0P.digestTarget (FIw_PublicModel.ofPublic p) key)) old := by
  induction n generalizing start old with
  | zero=>rfl
  | succ n ih=>
    rw [FIy_FrontierLoop.model,ih (start+1) (by omega),List.ofFn_succ,List.foldl_cons]
    have step : (fun j : Fin (8#usize).val=>old j+FIy_FrontierMeaning.increment p.transition.live_snapshot s o.z start j.val)=
        R0P.digestAddBinding old (FIw_PublicModel.selector s
          (R0P.digestRow (FIw_PublicModel.ofPublic p) (.frontier ⟨start,by omega⟩)))
          (FIw_PublicModel.openings o).z (R0P.digestStart (FIw_PublicModel.ofPublic p) (.frontier ⟨start,by omega⟩))
          (R0P.digestTarget (FIw_PublicModel.ofPublic p) (.frontier ⟨start,by omega⟩)) := by
      funext j
      rw [FIz_DigestFrontier.value p o s ⟨start,by omega⟩ j]
      rfl
    rw [step]
    have indices : (List.ofFn (fun i : Fin n=>R0P.DigestKey.frontier ⟨start+1+i.val,by omega⟩))=
        List.ofFn (fun i : Fin n=>R0P.DigestKey.frontier ⟨start+i.succ.val,by omega⟩) := by
      apply congrArg List.ofFn
      funext i
      apply congrArg R0P.DigestKey.frontier
      apply Fin.ext
      change start+1+i.val=start+(i.val+1)
      omega
    rw [indices]
    simp only [Fin.val_zero,Nat.add_zero]
#print axioms value
end AspisR1.FIz_DigestFold
end
