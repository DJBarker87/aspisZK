import FJh_InternalAccumulateLimbs
import RawPoseidonExtensionWords

/-! Source state coordinates for the internal accumulator. The Nat-indexed
view is total solely to avoid proof-indexed getters in symbolic sums; the
source read lemma binds it to the actual in-range cell. -/
set_option autoImplicit false
namespace AspisR1.FJh_InternalStateWords
open Aeneas Aeneas.Std Result
open FIq_Native
open AspisR1.FJh_Base (State QM Canonical CanonicalState cell)
open AspisR1.FJh_InternalClosureSums (Words4 CanonicalWords)

def wordVec (q : QM) : Words4 := Array.make 4#usize [q.c0.a,q.c0.b,q.c1.a,q.c1.b]

def wordNat (state : State) (lane : Nat) (limb : Fin 4) : Nat :=
  match state.val[lane]? with
  | none => 0
  | some q => (cell (wordVec q) limb).val

theorem wordVec_source (q : QM) : state_only_poseidon.extension_limbs q = .ok (wordVec q) := rfl

theorem wordVec_canonical (q : QM) (hq : Canonical q) : CanonicalWords (wordVec q) := by
  intro j
  fin_cases j
  · exact hq.1.1
  · exact hq.1.2
  · exact hq.2.1
  · exact hq.2.2

theorem state_source_read (state : State) (lane : Usize) (hlane : lane.val < 16) :
    Array.index_usize state lane = .ok (cell state (⟨lane.val,hlane⟩ : Fin 16)) := by
  have hb : lane.val < (16#usize).val := by simpa using hlane
  simpa only [cell] using AspisR1.ExtractedMaskHornerStep.array_index_usize_ok state lane hb

theorem wordNat_read (state : State) (lane : Usize) (hlane : lane.val < 16) (limb : Fin 4) :
    wordNat state lane.val limb =
      (cell (wordVec (cell state (⟨lane.val,hlane⟩ : Fin 16))) limb).val := by
  unfold wordNat
  rw [List.getElem?_eq_getElem (by simpa [state.property] using hlane)]
  rfl

/-- A symbolic natural sum in the source's forward lane order. -/
def remaining (state : State) (start : Nat) (fuel : Nat) (limb : Fin 4) : Nat :=
  match fuel with
  | 0 => 0
  | n+1 => wordNat state start limb + remaining state (start+1) n limb

#print axioms wordVec_source
#print axioms wordVec_canonical
#print axioms state_source_read
#print axioms wordNat_read
end AspisR1.FJh_InternalStateWords
