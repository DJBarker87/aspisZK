import R1Z.ProverCommitQArray48
import Mathlib.Tactic.FinCases
/-! Generic seven-cell storage identities, isolated before composing large
arithmetic result terms. -/
set_option autoImplicit false
namespace R1Z.ProverCommitRawVector49
open Aeneas Aeneas.Std AspisR1ProducerRelease47
open ProverCommitPrimitive47 ProverCommitSubfieldOps47

def values (a b c d e f g : Old.Q) (i : Nat) : Old.Q :=
  if i=0 then a else if i=1 then b else if i=2 then c else if i=3 then d
  else if i=4 then e else if i=5 then f else g

theorem array_values (a b c d e f g : Old.Q) :
    ProverCommitQArray48.array 7#usize (values a b c d e f g)=
      Array.make 7#usize [ProverCommitNativeQ48.source a,ProverCommitNativeQ48.source b,
        ProverCommitNativeQ48.source c,ProverCommitNativeQ48.source d,ProverCommitNativeQ48.source e,
        ProverCommitNativeQ48.source f,ProverCommitNativeQ48.source g] := by
  apply Subtype.ext
  rfl

theorem canonical (a b c d e f g : Old.Q)
    (ha : Canonical a) (hb : Canonical b) (hc : Canonical c) (hd : Canonical d)
    (he : Canonical e) (hf : Canonical f) (hg : Canonical g) (i : Nat) :
    Canonical (values a b c d e f g i) := by
  unfold values
  split_ifs <;> assumption

theorem map_values {K : Type} (v : Old.Q → K) (a b c d e f g : Old.Q) (k : Fin 7) :
    v (values a b c d e f g k.val)=![v a,v b,v c,v d,v e,v f,v g] k := by
  fin_cases k <;> rfl

#print axioms array_values
#print axioms canonical
#print axioms map_values
end R1Z.ProverCommitRawVector49
