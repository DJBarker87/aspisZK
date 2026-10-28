import R1Z.PV_RunJoin_OpeningWord43
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_OpeningLane43
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
abbrev W := aspis_core.field.wide_exact.WideExact

def row [ExternalFuns] (ops : ExternalFuns) (word : host_commitment.Word)
    (u : aspis_core.r0.domain.FibreIndex) : Result (Array W 4#usize) := do
  let i ← aspis_core.r0.domain.FibreIndex.get u
  let at1 ← Aeneas.Std.lift (Std.Usize.wrapping_mul 4#usize i)
  let we ← PV_RunJoin_OpeningWord43.read ops word at1
  let i1 ← Aeneas.Std.lift (Std.Usize.wrapping_add at1 1#usize)
  let we1 ← PV_RunJoin_OpeningWord43.read ops word i1
  let i2 ← Aeneas.Std.lift (Std.Usize.wrapping_add at1 2#usize)
  let we2 ← PV_RunJoin_OpeningWord43.read ops word i2
  let i3 ← Aeneas.Std.lift (Std.Usize.wrapping_add at1 3#usize)
  let we3 ← PV_RunJoin_OpeningWord43.read ops word i3
  ok (Array.make 4#usize [ we, we1, we2, we3 ])

/-- All four values are read from the actual stored word, in source order.
The FibreIndex operation and every Result failure remain in the execution. -/
theorem complete (ops : ExternalFuns) (word : host_commitment.Word)
    (u : aspis_core.r0.domain.FibreIndex) :
    @host_commitment.opening_lane_values _ (ProverRwP6BodyCandidate.selected ops) word u=
      @row _ (ProverRwP6BodyCandidate.selected ops) ops word u := by
  unfold host_commitment.opening_lane_values row
  apply congrArg (Aeneas.Std.bind _)
  funext i
  simp only [lift,bind_tc_ok]
  let at1 := Usize.wrapping_mul 4#usize i
  rw [PV_RunJoin_OpeningWord43.value ops word (at1)]
  apply congrArg (Aeneas.Std.bind _)
  funext value0
  rw [PV_RunJoin_OpeningWord43.value ops word (Usize.wrapping_add at1 1#usize)]
  apply congrArg (Aeneas.Std.bind _)
  funext value1
  rw [PV_RunJoin_OpeningWord43.value ops word (Usize.wrapping_add at1 2#usize)]
  apply congrArg (Aeneas.Std.bind _)
  funext value2
  rw [PV_RunJoin_OpeningWord43.value ops word (Usize.wrapping_add at1 3#usize)]
  apply congrArg (Aeneas.Std.bind _)
  funext value3
  rfl
#print axioms complete
end R1Z.PV_RunJoin_OpeningLane43
