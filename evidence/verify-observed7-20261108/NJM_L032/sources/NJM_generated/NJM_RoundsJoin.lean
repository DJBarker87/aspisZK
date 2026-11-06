import NJM_RoundNormalized
import NJM_RoundsInvariant
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJM_RoundsJoin
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NJG_RoundsCode
open PreparedHashCode (run)

def step {H : Type} (D : aspis_core.Digest32 H) (bytes : Slice U8)
 (pre : AspisR1PrefixAggregateParser.r1_wire.Prefix)
 (parsed : AspisR1PrefixAggregateParser.r1_wire.Prefix.parse bytes=ok (.Ok pre))
 (r : Usize) (carry : Carry H) : PreparedHashCode.Log × Result (Output H) :=
 if bound : r.val<10 then NJM_RoundNormalized.stage D bytes pre parsed carry.2.2 carry.2.1 carry.1 r bound
 else run (S1SemanticCode.roundStep NJM_RoundJoin.R D (PrefixAdapter.fromOld pre) carry.2.2 carry.2.1 carry.1 r)

def chain {H : Type} (D : aspis_core.Digest32 H) (bytes : Slice U8)
 (pre : AspisR1PrefixAggregateParser.r1_wire.Prefix)
 (parsed : AspisR1PrefixAggregateParser.r1_wire.Prefix.parse bytes=ok (.Ok pre)) :
 List Usize → Carry H → PreparedHashCode.Log × Result (Output H)
 | [],carry => ([],ok (.Ok carry))
 | r::rest,carry =>
   let one := step D bytes pre parsed r carry
   match one.2 with
   | .fail error => (one.1,.fail error)
   | .div => (one.1,.div)
   | .ok (.Err error) => (one.1,ok (.Err error))
   | .ok (.Ok next) =>
     let tail := chain D bytes pre parsed rest next
     (one.1++tail.1,tail.2)

theorem step_eq {H : Type} (D : aspis_core.Digest32 H) (bytes : Slice U8)
 (pre : AspisR1PrefixAggregateParser.r1_wire.Prefix)
 (parsed : AspisR1PrefixAggregateParser.r1_wire.Prefix.parse bytes=ok (.Ok pre))
 (r : Usize) (carry : Carry H) :
 run (S1SemanticCode.roundStep NJM_RoundJoin.R D (PrefixAdapter.fromOld pre) carry.2.2 carry.2.1 carry.1 r)=
 step D bytes pre parsed r carry := by
 unfold step
 split
 · exact NJM_RoundNormalized.source _ _ _ _ _ _ _ _ _
 · rfl

/-- Rule-B finite induction follows the SAME returned carry, never ten
independent posts. Every Rust rejection and outer abort keeps its full prefix. -/
theorem source {H : Type} (D : aspis_core.Digest32 H) (bytes : Slice U8)
 (pre : AspisR1PrefixAggregateParser.r1_wire.Prefix)
 (parsed : AspisR1PrefixAggregateParser.r1_wire.Prefix.parse bytes=ok (.Ok pre))
 (sites : List Usize) (carry : Carry H) :
 run (NJG_RoundsCode.chain NJM_RoundJoin.R D (PrefixAdapter.fromOld pre) sites carry)=
 chain D bytes pre parsed sites carry := by
 induction sites generalizing carry with
 | nil => rfl
 | cons r rest ih =>
   rw [NJM_RoundsInvariant.cons_run,step_eq D bytes pre parsed r carry]
   unfold chain
   generalize step D bytes pre parsed r carry = one
   rcases one with ⟨log,reply⟩
   cases reply with
   | fail error => rfl
   | div => rfl
   | ok result =>
     cases result with
     | Err e => simp only [NGX_RunBind.appendResult,NGX_CodeTrace.pure_run,List.append_nil]
     | Ok next =>
       simp only [NGX_RunBind.appendResult]
       rw [ih next]

#print axioms step_eq
#print axioms source
end AspisR1.NJM_RoundsJoin
end
