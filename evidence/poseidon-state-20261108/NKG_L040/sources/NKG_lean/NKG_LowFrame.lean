import NKG_OracleCuts
import NKG_InternalChoices
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKG_LowFrame
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon)
open FIw_ArrayValue (canonical)
open FJh_Base (cell)
open FJa_PoseidonOrigins (Selectors)
open NKG_InternalChoices (get get_ok)
def index (r : Fin 16) : Usize := Usize.ofNat r.val (by have := r.isLt;scalar_tac)
def step (s : Selectors) (acc : NQ) (r : Fin 16) :=
 get (field.QM31.add acc (cell s.local r)) field.QM31.ZERO
def Steps (s : Selectors) (rows : List (Fin 16)) (states : Nat → NQ) : Prop :=
 ∀ n (hn : n<rows.length),∃ args calls,NKG_OracleCuts.Low s.local (states n) (rows[n]'hn)
   (step s (states n) (rows[n]'hn)) (states (n+1)) args calls
structure Trace (s : Selectors) (rows : List (Fin 16)) (states : Nat → NQ) : Prop where
 initial : states 0=field.QM31.ZERO
 steps : Steps s rows states
/-- One K017 native iteration, then induction over exactly the control rows
certified by K051/K052. No whole-buffer arithmetic native proof. -/
theorem loop (N : Usize) (rows : List (Fin 16)) (s : Selectors) (states : Nat → NQ)
 (hs : canonical s.local) (hc : Canon (states 0)) (cuts : Steps s rows states) :
 core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.fold (N:=N)
   FJa_LocalWeightFold.Callback (rows.map index) (states 0) s=ok (states rows.length) ∧
 Canon (states rows.length) := by
 induction rows generalizing states with
 | nil => exact ⟨rfl,hc⟩
 | cons r rows ih =>
   have rr : Array.index_usize s.local (index r)=ok (cell s.local r) :=
     RawPoseidonExternalRowReads.array_index_usize_ok s.local (index r) r.isLt
   obtain ⟨next,ra,cn,_⟩ := FIv_PreparedTotal.add (states 0) (cell s.local r) hc (hs _ (List.getElem_mem _))
   have valueStep : step s (states 0) r=next := get_ok _ _ _ ra
   obtain ⟨args,calls,head⟩ := cuts 0 (by simp)
   have same : states 1=next := head.returned.trans valueStep
   have cb : FJa_LocalWeightStep.Call s (states 0,index r)=ok (next,s) := by
     change (do let q ← Array.index_usize s.local (index r)
                let q1 ← field.QM31.add (states 0) q
                ok (q1,s))=ok (next,s)
     rw [rr,bind_tc_ok,ra,bind_tc_ok]
   have tailSteps : Steps s rows (fun n=>states (n+1)) := by
     intro n hn
     simpa only [Nat.add_one,List.getElem_cons_succ] using cuts (n+1) (by simpa only [List.length_cons] using Nat.succ_lt_succ hn)
   have tail := ih (fun n=>states (n+1)) (same.symm ▸ cn) tailSteps
   refine ⟨?_,tail.2⟩
   change core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.fold
     FJa_LocalWeightFold.Callback (index r::rows.map index) (states 0) s=ok (states (rows.length+1))
   have cb' : FJa_LocalWeightFold.Callback.call_mut s (states 0,index r)=ok (next,s) := cb
   rw [core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.fold,cb',bind_tc_ok]
   change core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.fold
     FJa_LocalWeightFold.Callback (rows.map index) next s=ok (states (rows.length+1))
   rw [←same]
   exact tail.1

def fullRows : List (Fin 16) := [⟨1,by decide⟩,⟨9,by decide⟩,⟨10,by decide⟩]
def internalRows : List (Fin 16) := [⟨2,by decide⟩,⟨3,by decide⟩,⟨4,by decide⟩,⟨5,by decide⟩,⟨6,by decide⟩,⟨7,by decide⟩,⟨8,by decide⟩]
theorem full (s : Selectors) (states : Nat → NQ) (hs : canonical s.local)
 (cut : Trace s fullRows states) : FJa_PoseidonOrigins.fullFold s=ok (states 3) ∧ Canon (states 3) := by
 have h := loop 3#usize fullRows s states hs (cut.initial.symm ▸ FIv_NativeValue.zero.1) cut.steps
 rw [cut.initial] at h
 refine ⟨?_,h.2⟩
 unfold FJa_PoseidonOrigins.fullFold
 simp only [FIq_Native.Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter,bind_tc_ok]
 exact h.1

theorem internal (s : Selectors) (states : Nat → NQ) (hs : canonical s.local)
 (cut : Trace s internalRows states) : FJa_PoseidonOrigins.internalFold s=ok (states 7) ∧ Canon (states 7) := by
 have h := loop 7#usize internalRows s states hs (cut.initial.symm ▸ FIv_NativeValue.zero.1) cut.steps
 rw [cut.initial] at h
 rw [FJa_InternalLowShape.value]
 exact h
#print loop
#print axioms loop
#print full
#print axioms full
#print internal
#print axioms internal
end AspisR1.NKG_LowFrame
end
