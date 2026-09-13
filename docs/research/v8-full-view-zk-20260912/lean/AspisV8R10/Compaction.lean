import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.Abel

set_option autoImplicit false
namespace AspisV8R10
variable {K : Type*} [AddCommGroup K]

structure CompactRoundSource (K : Type*) where
  c0 : K
  c1 : K
  tail : Fin 26 → K

def roundBoundary (r : CompactRoundSource K) : K :=
  r.c0 + r.c0 + r.c1 + ∑ i, r.tail i

def compactRound (r : CompactRoundSource K) : K × (Fin 26 → K) :=
  (r.c0, r.tail)

def decodeRound (boundary : K) (sent : K × (Fin 26 → K)) : CompactRoundSource K :=
  ⟨sent.1, boundary - (sent.1 + sent.1) - ∑ i, sent.2 i, sent.2⟩

theorem decode_compact_round (r : CompactRoundSource K) :
    decodeRound (roundBoundary r) (compactRound r) = r := by
  rcases r with ⟨a, b, t⟩
  change (⟨a, (a + a + b + ∑ i, t i) - (a + a) - ∑ i, t i, t⟩ : CompactRoundSource K) =
    ⟨a, b, t⟩
  congr 1
  abel

theorem compact_injective_at_fixed_boundary (r s : CompactRoundSource K)
    (hb : roundBoundary r = roundBoundary s) (hs : compactRound r = compactRound s) :
    r = s := by
  calc
    r = decodeRound (roundBoundary r) (compactRound r) := (decode_compact_round r).symm
    _ = decodeRound (roundBoundary s) (compactRound s) := by rw [hb, hs]
    _ = s := decode_compact_round s

#print axioms decode_compact_round
#print axioms compact_injective_at_fixed_boundary
end AspisV8R10
