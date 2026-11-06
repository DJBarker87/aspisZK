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
 | [],carry=>pure (.Ok carry)
 | round::rest,carry=>do
   let reply←S1SemanticCode.roundStep B D pre carry.2.2 carry.2.1 carry.1 round
   let cf←core.result.Result.Insts.CoreOpsTry.branch reply
   match cf with
   | .Continue next=>chain B D pre rest next
   | .Break residual=>core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (Carry H) (core.convert.FromSame r1_wire.Error) residual

def source {H : Type} (B : RoundModel.Boundaries) (D : aspis_core.Digest32 H)
 (pre : r1_wire.Prefix) (t : r1_wire.SemanticTranscript H) : Code (Output H) := do
 let reply←r1_wire.Prefix.validated_record pre 14#u8
 let cf←core.result.Result.Insts.CoreOpsTry.branch reply
 match cf with
 | .Continue record=>
   let decoded←B.decode 1#usize record 0#usize
   let cf←core.result.Result.Insts.CoreOpsTry.branch decoded
   match cf with
   | .Continue values=>
     let running←Array.index_usize values 0#usize
     let alpha:=Array.repeat 10#usize Q.ZERO
     chain B D pre sites (running,alpha,t)
   | .Break residual=>core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (Carry H) (core.convert.FromSame r1_wire.Error) residual
 | .Break residual=>core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
    (Carry H) (core.convert.FromSame r1_wire.Error) residual

/-- Original ten unrolled source calls equal the finite source chain literally,
including every Try/Result stage, transcript and carry. No returning child or
successful parent is a premise. Native one-site cut still needs row133. -/
theorem unrolled {H : Type} (B : RoundModel.Boundaries) (D : aspis_core.Digest32 H)
 (pre : r1_wire.Prefix) (t : r1_wire.SemanticTranscript H) :
 source B D pre t=S1SemanticCode.rounds B D pre t := rfl

theorem ordered_run {H : Type} (B : RoundModel.Boundaries) (D : aspis_core.Digest32 H)
 (pre : r1_wire.Prefix) (t : r1_wire.SemanticTranscript H) :
 run (source B D pre t)=run (S1SemanticCode.rounds B D pre t) := congrArg run (unrolled B D pre t)

theorem sites_domain (round : Usize) (member : round∈sites) : round.val<10 := by
 simp only [sites,List.mem_cons,List.mem_singleton] at member
 rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

#print axioms unrolled
#print axioms ordered_run
#print axioms sites_domain
end AspisR1.NJG_RoundsCode
