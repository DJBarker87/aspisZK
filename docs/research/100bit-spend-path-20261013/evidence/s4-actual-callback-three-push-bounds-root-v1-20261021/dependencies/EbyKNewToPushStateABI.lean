import EbyKNewCutProof
import EbyKPushExplicitTypesV1
import Aeneas
open Aeneas Aeneas.Std Result
set_option autoImplicit false

namespace EbyKNewToPushStateABI

abbrev OldDot := AspisR1Stage2Accumulate.fast_pairing.canonical.Dot
abbrev OldState := AspisR1Stage2Accumulate.fast_pairing.EbyKDot
abbrev PushDot := AspisR1EbyKPushCutV3.fast_pairing.canonical.Dot
abbrev PushState := AspisR1EbyKPushCutV3.fast_pairing.EbyKDot

def dotToPush (d : OldDot) : PushDot := { sums := d.sums }
def stateToPush (s : OldState) : PushState :=
  { c0 := dotToPush s.c0, c1 := dotToPush s.c1, count := s.count }

def pushZero : PushState :=
  { c0 := { sums := Array.repeat 4#usize 0#u64 },
    c1 := { sums := Array.repeat 4#usize 0#u64 }, count := 0#usize }

def oldZero : OldState :=
  { c0 := { sums := Array.repeat 4#usize 0#u64 },
    c1 := { sums := Array.repeat 4#usize 0#u64 }, count := 0#usize }

theorem constructor_new_push_state_compatible :
    ∃ old : OldState,
      AspisR1Stage2Accumulate.new_entry = .ok old ∧
      stateToPush old = pushZero := by
  refine ⟨oldZero, EbyKNewCutProof.public_entry_new_zero, ?_⟩
  rfl

#print axioms constructor_new_push_state_compatible
end EbyKNewToPushStateABI
