import NJB_StubLaws
import NJB_ActiveRegroup
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJB_ActiveModel
variable {K : Type} [Field K]
def key (b : Fin 64) : Fin 7 := R0P.activeMaskCoordinate (R0P.copyActiveRowMasks b)
def highStep (h : Fin 64 → K) (state : Fin 7 → K) (b : Fin 64) : Fin 7 → K :=
 fun c => if key b=c then state c+h b else state c
def highRun (h : Fin 64 → K) : List (Fin 64) → (Fin 7 → K) → Fin 7 → K
 | [],state => state
 | b::bs,state => highRun h bs (highStep h state b)
theorem high_prefix (h : Fin 64 → K) (bs : List (Fin 64)) (state : Fin 7 → K) (c : Fin 7) :
 highRun h bs state c=state c+(bs.map (fun b => if key b=c then h b else 0)).sum := by
 induction bs generalizing state with
 | nil => simp [highRun]
 | cons b bs ih =>
  rw [highRun,ih]
  by_cases same : key b=c <;> simp [highStep,same,List.map_cons,List.sum_cons] <;> ring
theorem high_complete (h : Fin 64 → K) :
 highRun h (List.ofFn (fun b : Fin 64 => b)) (fun _ => 0)=R0P.activeMaskGroupedHigh h := by
 funext c
 change highRun h (List.ofFn (fun b : Fin 64 => b)) (fun _ => 0) c =
  ∑ b : Fin 64, if key b=c then h b else 0
 rw [high_prefix,zero_add,List.map_ofFn,List.sum_ofFn]
def weight (low : Fin 16 → K) (c : Fin 7) : K :=
 R0P.activeMaskLowSum low (R0P.activeMaskBasisMasks c)
def lowStep (h : Fin 7 → K) (low : Fin 16 → K) (sum : K) (c : Fin 7) : K :=
 sum+h c*weight low c
def lowRun (h : Fin 7 → K) (low : Fin 16 → K) : List (Fin 7) → K → K
 | [],sum => sum
 | c::cs,sum => lowRun h low cs (lowStep h low sum c)
theorem low_prefix (h : Fin 7 → K) (low : Fin 16 → K) (cs : List (Fin 7)) (sum : K) :
 lowRun h low cs sum=sum+(cs.map (fun c => h c*weight low c)).sum := by
 induction cs generalizing sum with
 | nil => simp [lowRun]
 | cons c cs ih => simp [lowRun,ih,lowStep,List.map_cons,List.sum_cons,add_assoc]
def reference (s : R0P.CopySelectors K) : K :=
 lowRun (highRun s.high (List.ofFn (fun b : Fin 64 => b)) (fun _ => 0)) s.low
  (List.ofFn (fun c : Fin 7 => c)) 0
/-- Symbolic finite induction and regrouping. No concrete recurrence is normalized. -/
theorem result (s : R0P.CopySelectors K) : reference s=R0P.copyActiveLiteral s := by
 rw [reference,high_complete,low_prefix,zero_add,List.map_ofFn,List.sum_ofFn]
 exact (R0P.copy_active_literal_eq_active_mask_basis s).symm
#print axioms high_prefix
#print axioms high_complete
#print axioms low_prefix
#print axioms result
end AspisR1.NJB_ActiveModel
end
