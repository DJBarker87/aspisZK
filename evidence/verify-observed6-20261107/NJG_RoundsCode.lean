import NJG_RoundCode
set_option autoImplicit false
namespace AspisR1.NJG_RoundsCode
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open PreparedHashCode (Code run)
abbrev Q := aspis_core.field.QM31
abbrev Carry (H : Type) := Q × Array Q 10#usize × r1_wire.SemanticTranscript H
abbrev Output (H : Type) := core.result.Result (Carry H) r1_wire.Error

def sites : List Usize := [0#usize,1#usize,2#usize,3#usize,4#usize,5#usize,6#usize,7#usize,8#usize,9#usize]

def chain {H : Type} (B : RoundModel.Boundaries) (D : aspis_core.Digest32 H)
    (pre : r1_wire.Prefix) : List Usize → Carry H → Code (Output H)
  | [],carry => pure (.Ok carry)
  | round::rest,carry => do
    let reply ← S1SemanticCode.roundStep B D pre carry.2.2 carry.2.1 carry.1 round
    let cf ← core.result.Result.Insts.CoreOpsTry.branch reply
    match cf with
    | .Continue next => chain B D pre rest next
    | .Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        (Carry H) (core.convert.FromSame r1_wire.Error) residual

def source {H : Type} (B : RoundModel.Boundaries) (D : aspis_core.Digest32 H)
    (pre : r1_wire.Prefix) (t : r1_wire.SemanticTranscript H) : Code (Output H) := do
  let reply ← r1_wire.Prefix.validated_record pre 14#u8
  let cf ← core.result.Result.Insts.CoreOpsTry.branch reply
  match cf with
  | .Continue record =>
    let decoded ← B.decode 1#usize record 0#usize
    let cf ← core.result.Result.Insts.CoreOpsTry.branch decoded
    match cf with
    | .Continue values =>
      let running ← Array.index_usize values 0#usize
      let alpha := Array.repeat 10#usize aspis_core.field.QM31.ZERO
      chain B D pre sites (running,alpha,t)
    | .Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        (Carry H) (core.convert.FromSame r1_wire.Error) residual
  | .Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (Carry H) (core.convert.FromSame r1_wire.Error) residual

/-- Definition-only preflight; the formerly heartbeat-limited ten-call join
is split into NJG_RoundsUnrolled and treats roundStep as an opaque callee. -/
theorem sites_domain (round : Usize) (member : round∈sites) : round.val<10 := by
 simp only [sites,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

#print axioms sites_domain
end AspisR1.NJG_RoundsCode
