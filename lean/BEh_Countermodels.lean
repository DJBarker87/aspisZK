import BEh_Scope
set_option autoImplicit false
namespace AspisR1.BEh_Countermodels
open Aeneas Aeneas.Std Result SdkC_Source BEh_Scope

/-- Inhabited acceptance and identical logs still do not determine erased state.
This tests the interface implication, not shipped Rust. -/
theorem accepted_log_not_carrier :
    let n : Outcome Bool Unit Unit := (.ok (.Ok ()),false,[])
    let s : Outcome Bool Unit Unit := (.ok (.Ok ()),true,[])
    n.1 = s.1 ∧ n.2.2 = s.2.2 ∧ ¬ Law n s := by
  refine ⟨rfl,rfl,?_⟩
  intro law
  have bad : false = true := congrArg Prod.fst (law.1.2 () rfl)
  cases bad

/-- The ruling permits distinct rejected errors and final states with a common
attempt prefix. Thus BEg observe equality cannot be REQUIRED for closure. -/
theorem rejected_state_not_required (before : Log) :
    let n : Outcome Bool Unit Unit := (.ok (.Err ()),false,before)
    let s : Outcome Bool Unit Unit := (.fail .panic,true,before)
    Law n s ∧ BEg_Observation.observe n ≠ BEg_Observation.observe s := by
  constructor
  · refine ⟨⟨?_,fun _ h => by cases h⟩,⟨Iff.rfl,fun _ => rfl⟩⟩
    intro a
    constructor <;> intro h <;> cases h
  · intro same
    have bad : false = true := congrArg (fun x => x.2.1) same
    cases bad

/-- An occurrence bound on each history does not associate their order. -/
theorem counts_not_association {T : Type} (a b : T) (different : a ≠ b) :
    [a,b].length = [b,a].length ∧ ([a,b] : List T) ≠ [b,a] := by
  refine ⟨rfl,?_⟩
  intro same
  exact different (List.cons.inj same).1

/-- Equal returns and even an EXACT ideal budget can coexist with an omitted
physical rejected attempt. This is a tiny recorder-interface countermodel. -/
theorem rejected_result_not_history (query : Query) :
    let n : Outcome Unit Unit Unit := (.ok (.Err ()),(),[query])
    let s : Outcome Unit Unit Unit := (.fail .panic,(),[])
    BEg_Observation.accepted n.1 = BEg_Observation.accepted s.1 ∧
    s.2.2.length = 0 ∧ ¬ Law n s := by
  refine ⟨rfl,rfl,?_⟩
  intro law
  have bad := law.2.2 rfl
  cases bad

#print axioms accepted_log_not_carrier
#print axioms rejected_state_not_required
#print axioms counts_not_association
#print axioms rejected_result_not_history
end AspisR1.BEh_Countermodels
