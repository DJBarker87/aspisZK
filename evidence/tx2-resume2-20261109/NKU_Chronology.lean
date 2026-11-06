import NKU_State
import NKK_LogAlgebra
import NKK_Try
set_option autoImplicit false
namespace NKU_Chronology
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission
abbrev Run (A : Type) := NJU_Log.Run NJU_ResumeObserved.Event A
abbrev Stage (A : Type) := NKU.State → Run (core.result.Result (A × NKU.State) verifier.Error)
def bind {A B : Type} (head : Stage A) (tail : A → Stage B) : Stage B :=
 fun s => do
 let reply ← head s
 NKK_Try.emitted reply (fun (a,post) => tail a post)
/-- SAME returned state starts the next cut, rather than another witness. -/
theorem next {A B : Type} (head : Stage A) (tail : A → Stage B)
 (s post : NKU.State) (a : A)
 (returned : (head s).result=.ok (.Ok (a,post))) :
 (bind head tail s).result=(tail a post).result ∧
 (bind head tail s).events=(head s).events++(tail a post).events := by
 unfold bind
 cases h : head s with
 | mk result events =>
  rw [h] at returned
  cases returned
  exact ⟨rfl,rfl⟩
theorem reject {A B : Type} (head : Stage A) (tail : A → Stage B)
 (s : NKU.State) (err : verifier.Error)
 (rejected : (head s).result=.ok (.Err err)) :
 (bind head tail s).result=.ok (.Err err) ∧
 (bind head tail s).events=(head s).events := by
 unfold bind
 cases h : head s with
 | mk result events =>
  rw [h] at rejected
  cases rejected
  exact ⟨rfl,List.append_nil _⟩
theorem abort {A B : Type} (head : Stage A) (tail : A → Stage B)
 (s : NKU.State) (err : Error) (failed : (head s).result=.fail err) :
 (bind head tail s).result=.fail err ∧ (bind head tail s).events=(head s).events :=
 NJU_Log.fail_prefix (head s) err failed _
theorem diverge {A B : Type} (head : Stage A) (tail : A → Stage B)
 (s : NKU.State) (failed : (head s).result=.div) :
 (bind head tail s).result=.div ∧ (bind head tail s).events=(head s).events :=
 NJU_Log.div_prefix (head s) failed _
#print axioms next
#print axioms reject
#print axioms abort
#print axioms diverge
end NKU_Chronology
