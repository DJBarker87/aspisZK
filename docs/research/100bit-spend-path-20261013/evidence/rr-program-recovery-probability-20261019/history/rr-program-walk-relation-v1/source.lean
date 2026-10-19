import RRProgramTraversal

namespace AspisR1.RRProgramWalkRelation
open AspisR1.RRProgramTraversal AspisR1.SequentialProgramInvariants
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

/-- Records the actual successful child outputs, in occurrence order.
Repeated states may have different randomized output orderings. -/
inductive WalkResult {K S : Type} (P : S → List (List K) → Prop) :
    List (K × S) → List (List K) → Prop
  | nil : WalkResult P [] []
  | cons (a : K) (s : S) (tail : List (K × S)) (ys zs : List (List K))
      (head : P s ys) (rest : WalkResult P tail zs) :
      WalkResult P ((a,s)::tail) (ys.map (a :: ·) ++ zs)

theorem walkChildren_all {I A K S : Type}
    (run : S → Program I A (Option (List (List K))))
    (P : S → List (List K) → Prop)
    (hrun : ∀ s, AllOutcomes (run s) (fun out => ∀ ys, out = some ys → P s ys))
    (cs : List (K × S)) :
    AllOutcomes (walkChildren run cs)
      (fun out => ∀ ys, out = some ys → WalkResult P cs ys) := by
  induction cs with
  | nil =>
    intro ys hs
    cases hs
    exact .nil
  | cons pair tail ih =>
    rcases pair with ⟨a,s⟩
    rw [walkChildren, optionBind]
    apply all_bind
    apply all_mono _ (hrun s)
    intro head hhead
    cases head with
    | none =>
      intro ys hs
      contradiction
    | some ys =>
      rw [mapOption]
      apply all_bind
      apply all_mono _ ih
      intro rest hrest
      cases rest with
      | none =>
        intro zs hs
        contradiction
      | some zs =>
        intro out hs
        cases hs
        exact .cons a s tail ys zs (hhead ys rfl) (hrest zs rfl)

#print axioms WalkResult
#print axioms walkChildren_all
end AspisR1.RRProgramWalkRelation
