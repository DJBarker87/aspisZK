import R1Z.PV_RJQ_QueryInvariant
set_option autoImplicit false
namespace R1Z.PV_RJQ_QueryScan
open Aeneas Aeneas.Std Result ProverRwFull ProverRwQueryScan
open PV_RunJoin_ResultPost PV_RJQ_QueryInvariant
variable [ExternalTypes] [ExternalFuns]
def Good (r : Output) : Prop := match r with
  | .Ok (q,_) => Bounded q
  | .Err _ => True

theorem dispatch (blocks advances : Blocks) (accepted : Queries) (n draws : Usize)
    (recur : Queries → Usize → Usize → Result Output)
    (hq : Bounded accepted)
    (hr : ∀ a m d, Bounded a → Post Good (recur a m d)) :
    Post Good (ProverRwQueryScan.dispatch recur blocks advances accepted n draws) := by
  unfold ProverRwQueryScan.dispatch
  split
  · split
    · apply bind_right; intro a
      exact ok Good _ hq
    · exact ok Good _ True.intro
  · apply bind_right; intro k
    split
    · apply bind_right; intro a
      exact ok Good _ hq
    · simp only [lift,bind_tc_ok]
      apply bind_right; intro i
      apply bind_right; intro a
      apply bind_right; intro b0
      apply bind_right; intro b1
      apply bind_right; intro b2
      apply bind_right; intro b3
      apply bind_right; intro duplicate
      split
      · exact hr _ _ _ hq
      · apply bind_known Good Bounded _ _ (update _ _ _ hq (mask _))
        intro updated hu
        exact hr _ _ _ hu

theorem finite (blocks advances : Blocks) (fuel : Nat) (accepted : Queries)
    (n draws : Usize) (hq : Bounded accepted) :
    Post Good (ProverRwQueryScan.finite blocks advances fuel accepted n draws) := by
  induction fuel generalizing accepted n draws with
  | zero =>
    apply dispatch blocks advances accepted n draws _ hq
    intro a m d ha out h
    cases h
  | succ fuel ih =>
    apply dispatch blocks advances accepted n draws _ hq
    exact ih

theorem pairs (blocks advances : Blocks) (q : Queries) (state : Array U8 32#usize)
    (h : host_transcript.queries_from_pairs blocks advances=ok (.Ok (q,state))) :
    Bounded q := by
  rw [queries_finite] at h
  exact finite blocks advances 64 _ _ _ initial _ h

#print axioms dispatch
#print axioms finite
#print axioms pairs
end R1Z.PV_RJQ_QueryScan
