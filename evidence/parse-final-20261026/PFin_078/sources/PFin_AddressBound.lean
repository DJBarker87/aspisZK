import OraclePortFrozen2Bounds
set_option autoImplicit false
noncomputable section
namespace AspisR1.PFin_AddressBound
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

def Bounded {O : Type} (p : Program Bytes State O) : Prop :=
  ∀ H x,x∈(eval H p).1 → x.1.length≤514

theorem done {O : Type} (o : O) : Bounded (.done o) := by
  intro H x member
  cases member

theorem ask {O : Type} (a : Bytes) (k : State → Program Bytes State O)
    (small : a.length≤514) (cont : ∀ answer,Bounded (k answer)) : Bounded (.ask a k) := by
  intro H x member
  simp only [eval,List.mem_cons] at member
  rcases member with same | later
  · simpa only [same] using small
  · exact cont (H a) H x later

theorem bind {O P : Type} (p : Program Bytes State O) (k : O → Program Bytes State P)
    (first : Bounded p) (rest : ∀ o,Bounded (k o)) : Bounded (OracleProgramOps.bind p k) := by
  intro H x member
  simp only [eval_bind,List.mem_append] at member
  rcases member with old | later
  · exact first H x old
  · exact rest (eval H p).2 H x later

#print axioms done
#print axioms ask
#print axioms bind
end AspisR1.PFin_AddressBound
end
