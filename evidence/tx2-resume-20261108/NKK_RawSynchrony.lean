import NKK_RunEval
set_option autoImplicit false
noncomputable section
namespace NKK_RawFold
open Aeneas Aeneas.Std Result NKK_NativeRaw

def Child {n : Usize} (e : Event n) : Prop :=
 e.reply=NJC_ConcreteUnwrap.raw n e.before

def Synchronized {n : Usize} : List (Event n) → State n → Prop
 | [],_ => True
 | e::es,state => state.status=.ok () ∧ e.before=state.reader ∧
   Synchronized es (step state e)

theorem clauses (n : Usize) (count : Nat) (r : Reader) :
 NKK_LogClauses.Holds Child (observed n count r) := by
 induction count generalizing r with
 | zero => exact NKK_LogClauses.pure _ _
 | succ count ih =>
  unfold observed
  apply NKK_LogClauses.bind
  · apply NKK_LogClauses.record
    rfl
  · rintro ⟨b,next⟩
    apply NKK_LogClauses.bind
    · exact ih next
    · rintro ⟨bs,last⟩
      exact NKK_LogClauses.pure _ _

/-- Every event is entered with the post-state of the immediately previous
source call. A failure contributes its one event and has no suffix. -/
theorem synchronized (n : Usize) (count : Nat) (r : Reader)
 (before : List (Array U8 n)) :
 Synchronized (observed n count r).events ⟨before,r,.ok ()⟩ := by
 induction count generalizing r before with
 | zero => trivial
 | succ count ih =>
  cases call : NJC_ConcreteUnwrap.raw n r with
  | fail err =>
   simp only [observed,NKK_RunEval.bind_eq,NKK_RunEval.pure_eq,
    NJU_Log.record,NJU_Log.bind,call,Synchronized]
   exact ⟨True.intro,True.intro,True.intro⟩
  | div =>
   simp only [observed,NKK_RunEval.bind_eq,NKK_RunEval.pure_eq,
    NJU_Log.record,NJU_Log.bind,call,Synchronized]
   exact ⟨True.intro,True.intro,True.intro⟩
  | ok pair =>
   rcases pair with ⟨b,next⟩
   have tail:=ih next (before++[b])
   cases rest : (observed n count next).result <;>
    simp only [observed,NKK_RunEval.bind_eq,NKK_RunEval.pure_eq,
     NJU_Log.record,NJU_Log.bind,call,rest,Synchronized,List.singleton_append,List.append_nil,step] <;>
    exact ⟨True.intro,True.intro,tail⟩

#print axioms clauses
#print axioms synchronized
end NKK_RawFold
