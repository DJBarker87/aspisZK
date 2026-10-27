import XRk_PushTrace
import XRk_DotCells
import XRk_PowersArray
open Aeneas Aeneas.Std Result
open XRk_Release XRk_ResultTools
namespace XRl_DotHistory
abbrev Input := XRk_Wide × aspis_core.field.QM31
/-- A chronological history of actual accepted emitted pushes, starting at
new. No scalar-canonicality or count bound is hidden in this predicate. -/
inductive Reached : List Input → fast_pairing.EbyKDot → Prop
  | initial (s : fast_pairing.EbyKDot) (run : fast_pairing.EbyKDot.new = ok s) : Reached [] s
  | push {xs : List Input} {old next : fast_pairing.EbyKDot}
      (prior : Reached xs old) (e : XRk_Wide) (q : aspis_core.field.QM31)
      (run : fast_pairing.EbyKDot.push old e q = ok (.Ok (),next)) :
      Reached (xs ++ [(e,q)]) next

theorem initial_count (s : fast_pairing.EbyKDot)
    (run : fast_pairing.EbyKDot.new = ok s) : s.count = 0#usize := by
  have same := congrArg fast_pairing.EbyKDot.count (Result.ok.inj run)
  exact same.symm

theorem count (xs : List Input) (s : fast_pairing.EbyKDot) (history : Reached xs s) :
    s.count.val = xs.length ∧ xs.length ≤ 4096 := by
  induction history with
  | initial s run =>
    rw [initial_count s run]
    constructor <;> simp
  | push prior e q run ih =>
    have hc := XRk_DotProjection.push_count _ _ e q run
    have hv := XRk_PowersArray.add_one_value _ 4096#usize _ hc.1 hc.2
    have hb : (4096#usize).val = 4096 := by scalar_tac
    simp only [List.length_append,List.length_singleton]
    constructor
    · omega
    · have below := hc.1
      change (UScalar.val _) < (4096#usize).val at below
      omega

theorem canonical_scalars (xs : List Input) (s : fast_pairing.EbyKDot) (history : Reached xs s) :
    ∀ v ∈ xs, XRk_CanonicalScalar.Canonical v.2 := by
  induction history with
  | initial s run => intro v member; cases member
  | push prior e q run ih =>
    intro v member
    rcases List.mem_append.mp member with old | last
    · exact ih v old
    · have same := List.mem_singleton.mp last
      subst v
      exact (XRk_PushTrace.accepted _ _ e q run).1

#print axioms initial_count
#print axioms count
#print axioms canonical_scalars
end XRl_DotHistory
