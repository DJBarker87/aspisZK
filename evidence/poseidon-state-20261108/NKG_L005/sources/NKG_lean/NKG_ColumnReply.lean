import NKG_ColumnLoop
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKG_ColumnReply
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIw_ArrayValue (canonical decoded)
open FJb_MatrixGroupStep (State)
open FJe_ThreeColumnStep (Weights model step)
open FJb_M31Step (Constants Bounded)
open FJb_TailCell (cell)
def scalarCell (w : Weights) (c0 c1 c2 : Constants) (i : Fin 16) : Result NQ :=
 FJe_ThreeCell.source (cell w ⟨0,by decide⟩) (cell w ⟨1,by decide⟩) (cell w ⟨2,by decide⟩)
   (cell c0 i) (cell c1 i) (cell c2 i)
def reply (w : Weights) (c0 c1 c2 : Constants) (i : Fin 16) : NQ :=
 match scalarCell w c0 c1 c2 i with
 | .ok q => q
 | _ => field.QM31.ZERO
/-- This is the value of four SAME-argument CLOSED scalar children; the fallback
is unreachable on the caller domain and is not a success-only premise. -/
theorem result (w : Weights) (c0 c1 c2 : Constants) (i : Fin 16)
 (hw : canonical w) (h0 : Bounded c0) (h1 : Bounded c1) (h2 : Bounded c2) :
 scalarCell w c0 c1 c2 i=ok (reply w c0 c1 c2 i) ∧
 FIv_NativeValue.Canon (reply w c0 c1 c2 i) := by
 have cw (j : Fin (3#usize).val) : FIv_NativeValue.Canon (cell w j) :=
   hw _ (List.getElem_mem _)
 obtain ⟨q,rq,cq,_⟩ := FJe_ThreeCell.source_success
   (cell w ⟨0,by decide⟩) (cell w ⟨1,by decide⟩) (cell w ⟨2,by decide⟩)
   (cell c0 i) (cell c1 i) (cell c2 i) (cw _) (cw _) (cw _) (h0 _) (h1 _) (h2 _)
 change scalarCell w c0 c1 c2 i=ok q at rq
 simp only [reply,rq]
 exact ⟨rq,cq⟩
/-- SAME returned raw reply is installed at exactly the source lane. -/
theorem step_reply (w : Weights) (c0 c1 c2 : Constants) (s : State) (i : Usize)
 (hi : i.val < 16) (hw : canonical w) (h0 : Bounded c0) (h1 : Bounded c1) (h2 : Bounded c2) :
 step w c0 c1 c2 s i=ok (s.set i (reply w c0 c1 c2 ⟨i.val,hi⟩)) := by
 have reads {A : Type} {n : Usize} (a : Array A n) (j : Usize) (hj : j.val<n.val) :
   Array.index_usize a j=ok (cell a ⟨j.val,hj⟩) := RawPoseidonExternalRowReads.array_index_usize_ok a j hj
 have rv := (result w c0 c1 c2 ⟨i.val,hi⟩ hw h0 h1 h2).1
 obtain ⟨out,ru,vu⟩ := WP.spec_imp_exists
   (Array.update_spec s i (reply w c0 c1 c2 ⟨i.val,hi⟩) (by simpa only [s.property] using hi))
 rw [vu] at ru
 simp only [step,reads w 0#usize (by decide),reads w 1#usize (by decide),reads w 2#usize (by decide),
   reads c0 i hi,reads c1 i hi,reads c2 i hi,bind_tc_ok]
 change (do let q ← scalarCell w c0 c1 c2 ⟨i.val,hi⟩;Array.update s i q)=_
 rw [rv,bind_tc_ok,ru]
#print result
#print axioms result
#print step_reply
#print axioms step_reply
end AspisR1.NKG_ColumnReply
end
