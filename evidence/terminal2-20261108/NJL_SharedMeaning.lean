import NJB_SharedReference
import NJB_PackLinearity
import RPv_FIx_SelectedMeaning
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJL_SharedMeaning
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (decode K)
open NJB_SharedReference (group lanes stepModel)
theorem group_injective : Function.Injective group := by
 intro g h e
 apply Fin.ext
 have v := congrArg Fin.val e
 dsimp only [group] at v
 omega
def increment (v : Fin 33 → NQ) (selector : NQ) (g : Fin 9) : K := decode selector*NJB_PackLaw.model (lanes v g)
theorem lane (v : Fin 33 → NQ) (selector : NQ) (g : Fin 9) (i : Fin 4) :
 decode selector*decode (lanes v g i)=FIx_SelectedMeaning.selected (fun k=>decode selector*decode (v k)) 49 (group g).val i.val := by
 dsimp only [lanes,FIx_SelectedMeaning.selected]
 split
 · rfl
 · rw [FIv_NativeValue.zero.2,mul_zero]
theorem contribution (v : Fin 33 → NQ) (selector : NQ) (g : Fin 9) :
 increment v selector g=FIx_SelectedMeaning.contribution (fun i=>decode selector*decode (v i)) 49 (group g).val := by
 rw [increment,NJB_PackLinearity.model,←NJB_PackLinearity.scale]
 unfold NJB_PackLinearity.pack FIx_SelectedMeaning.contribution FIx_PreweightedPack.pack
 dsimp only []
 rw [lane v selector g 0,lane v selector g 1,lane v selector g 2,lane v selector g 3]
 rfl
theorem outside (v : Fin 33 → NQ) (selector : NQ) (j : Fin 24) (out : j.val<12 ∨ 20<j.val) :
 FIx_SelectedMeaning.contribution (fun i=>decode selector*decode (v i)) 49 j.val=0 := by
 have hzero (i : Nat) (hi : i<4) : FIx_SelectedMeaning.selected (fun k=>decode selector*decode (v k)) 49 j.val i=0 := by
  dsimp only [FIx_SelectedMeaning.selected]
  split
  · omega
  · rfl
 unfold FIx_SelectedMeaning.contribution FIx_PreweightedPack.pack
 dsimp only []
 rw [hzero 0 (by decide),hzero 1 (by decide),hzero 2 (by decide),hzero 3 (by decide)]
 simp
theorem fold_prefix (v : Fin 33 → NQ) (selector : NQ) (gs : List (Fin 9)) (before : Fin 24 → K) (j : Fin 24) :
 (gs.foldl (fun s g=>stepModel v selector g s) before) j=
 before j+(gs.map (fun g=>if group g=j then increment v selector g else 0)).sum := by
 induction gs generalizing before with
 | nil => simp
 | cons g gs ih =>
  rw [List.foldl_cons,ih]
  by_cases h:group g=j
  · subst j;simp only [stepModel,NJB_StateUpdates.addModel,ite_true,increment,List.map_cons,List.sum_cons];ring
  · simp only [stepModel,NJB_StateUpdates.addModel,if_neg h,increment,List.map_cons,List.sum_cons,zero_add]
theorem value (v : Fin 33 → NQ) (selector : NQ) (before : Fin 24 → K) (j : Fin 24) :
 ((List.finRange 9).foldl (fun s g=>stepModel v selector g s) before) j=
 before j+FIx_SelectedMeaning.contribution (fun i=>decode selector*decode (v i)) 49 j.val := by
 rw [fold_prefix]
 congr 1
 change (List.ofFn (fun g : Fin 9=>if group g=j then increment v selector g else 0)).sum=_
 rw [List.sum_ofFn]
 by_cases inside : 12≤j.val ∧ j.val≤20
 · let g : Fin 9 := ⟨j.val-12,by omega⟩
   have same : group g=j := by apply Fin.ext;dsimp only [group,g];omega
   rw [←same]
   simp only [group_injective.eq_iff]
   simp only [Finset.sum_ite_eq',Finset.mem_univ,if_pos]
   exact contribution v selector g
 · have out : j.val<12 ∨ 20<j.val := by omega
   rw [outside v selector j out]
   apply Finset.sum_eq_zero
   intro g _
   have h : group g≠j := by intro e;have := congrArg Fin.val e;have := g.isLt;dsimp only [group] at *;omega
   exact if_neg h
#print axioms group_injective
#print axioms contribution
#print axioms outside
#print axioms fold_prefix
#print value
#print axioms value
end AspisR1.NJL_SharedMeaning
end
