import R1Z.PV_OWNP_SampleCarrier
set_option autoImplicit false
namespace R1Z.PV_OWNP_PassShape
open Aeneas Aeneas.Std PV_OWNO_SampleEight

theorem step_length (combine : U64 → U32 → U64) (s : State) (w : U32) :
 (step combine s w).words.length = s.words.length + 1 := by
 simp only [step,List.length_append,List.length_singleton]

theorem fold_length (combine : U64 → U32 → U64) (rank : List U32) (s : State) :
 (rank.foldl (step combine) s).words.length = s.words.length + rank.length := by
 induction rank generalizing s with
 | nil => simp only [List.foldl_nil,List.length_nil,Nat.add_zero]
 | cons w ws ih =>
  rw [List.foldl_cons,ih,step_length,List.length_cons]
  omega

theorem pass_length (combine : U64 → U32 → U64) (rank : List U32) :
 (pass combine rank).1.length = rank.length := by
 change (rank.foldl (step combine) ⟨[],0#u64⟩).words.length = rank.length
 rw [fold_length]
 rfl

/-- Every later division pass receives eight quotient words, including the
four passes whose returned digits are not selected for the QM31 result. -/
def ranks (combine : U64 → U32 → U64) : Nat → List U32 → List U32
 | 0,rank => rank
 | n+1,rank => ranks combine n (pass combine rank).1

theorem ranks_length (combine : U64 → U32 → U64) (n : Nat) (rank : List U32) :
 (ranks combine n rank).length = rank.length := by
 induction n generalizing rank with
 | zero => rfl
 | succ n ih => rw [ranks,ih,pass_length]

#print axioms step_length
#print axioms fold_length
#print axioms pass_length
#print axioms ranks_length
end R1Z.PV_OWNP_PassShape
