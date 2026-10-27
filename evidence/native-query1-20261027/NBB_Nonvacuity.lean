import NBB_RowWitness
import NBB_Finish
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace NBB_Nonvacuity
open S7Kani2OwnedRowRefinement (makeRow powerLimb)
def zeroPower : S7Kani2OwnedRow.K := ⟨(0#u32,0#u32),(0#u32,0#u32)⟩
def zeroRow : Fin 4 → U64 := fun _ => 0#u64

/-- The complete row domain and linked traces are inhabited at EVERY query
phase, including the source's flush phase. No native whole-query is claimed. -/
theorem row (terms : Nat) :
 ∃ (added : NBB_RowTrace.Row) (out : Fin 4 → U64),
 NBB_RowTrace.Steps (fun j r => r j+(powerLimb zeroPower j).val*(0#u32).val)
   [0,1,2,3] (fun j => (zeroRow j).val) added ∧
 (if decide (terms%4=3) then NBB_RowTrace.Steps
   (fun j r => AspisV8R17.RawReducer.foldBits (r j)) [0,1,2,3] added (fun j => (out j).val)
  else (fun j => (out j).val)=added) ∧
 S7Kani2OwnedRow.residue_owned (makeRow zeroRow) zeroPower 0#u32 (decide (terms%4=3))=
  ok (makeRow out) := by
 apply NBB_RowWitness.construct zeroRow zeroPower 0#u32 terms
 · intro j;fin_cases j <;> decide
 · decide
 · intro j
   change 0<2^34+(terms%4)*(2^31-2)^2
   omega

/-- A complete64-row cohort finish instance exists, without enumerating any
buffer or postulating an output or successful execution. -/
theorem finish : ∃ (b : AspisR1.Port3_FlushInstall.BW)
 (old out : Slice AspisR1.Port3_FlushInstall.K),
 b.raw.val.length=64 ∧ old.val.length=64 ∧
 AspisR1.Port3_FlushInstall.flush b old=ok out ∧ out.val.length=64 := by
 let z : AspisR1.Port3_FlushInstall.K := ⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩
 let raw : alloc.vec.Vec (Array U64 4#usize) :=
  ⟨List.replicate 64 (Array.repeat 4#usize 0#u64),by simp;scalar_tac⟩
 let b : AspisR1.Port3_FlushInstall.BW := ⟨raw,0#usize⟩
 let old : Slice AspisR1.Port3_FlushInstall.K := ⟨List.replicate 64 z,by simp;scalar_tac⟩
 have rb : b.raw.val.length=64 := by simp only [b,raw,List.length_replicate]
 have ob : old.val.length=64 := by simp only [old,List.length_replicate]
 obtain ⟨out,run,len,_,_⟩ := NBB_Finish.source b old rb ob
 exact ⟨b,old,out,rb,ob,run,len⟩
#print axioms row
#print axioms finish
end NBB_Nonvacuity
