import NJM_RoundsCut
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJM_RoundsInduction
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NJG_RoundsCode
open PreparedHashCode (run)

def one {H : Type} (native : NJM_RoundsCut.Observations) (token frame : Nat)
 (D : aspis_core.Digest32 H) (pre : r1_wire.Prefix) (r : Usize) (carry : Carry H) :=
 if bound : r.val<10 then NJM_RoundsCut.step native token frame D pre r bound carry
 else run (S1SemanticCode.roundStep NJM_RoundJoin.R D pre carry.2.2 carry.2.1 carry.1 r)

/-- Explicit chronological forward composition of the native one-call G.
Every error/abort terminates at that prefix. Only Ok passes the SAME next carry. -/
def chain {H : Type} (native : NJM_RoundsCut.Observations) (token frame : Nat)
 (D : aspis_core.Digest32 H) (pre : r1_wire.Prefix) :
 List Usize → Carry H → PreparedHashCode.Log × Result (Output H)
 | [],carry=>([],ok (.Ok carry))
 | r::rest,carry=>
   let head:=one native token frame D pre r carry
   match head.2 with
   | .fail e=>(head.1,.fail e)
   | .div=>(head.1,.div)
   | .ok (.Err e)=>(head.1,ok (.Err e))
   | .ok (.Ok next)=>
     let tail:=chain native token frame D pre rest next
     (head.1++tail.1,tail.2)

theorem one_source {H : Type} (native : NJM_RoundsCut.Observations) (cut : NJM_RoundsCut.Cut native)
 (token frame : Nat) (D : aspis_core.Digest32 H) (pre : r1_wire.Prefix) (r : Usize) (carry : Carry H) :
 one native token frame D pre r carry=run (S1SemanticCode.roundStep NJM_RoundJoin.R D pre carry.2.2 carry.2.1 carry.1 r) := by
 unfold one
 split
 · exact NJM_RoundsCut.source _ cut _ _ _ _ _ _ _
 · rfl

/-- Induction is over the actual native/source control sequence and actual
returned carries. The only protocol call is the fixed concrete133 child. -/
theorem source {H : Type} (native : NJM_RoundsCut.Observations) (cut : NJM_RoundsCut.Cut native)
 (token frame : Nat) (D : aspis_core.Digest32 H) (pre : r1_wire.Prefix)
 (rows : List Usize) (carry : Carry H) :
 chain native token frame D pre rows carry=
 run (NJG_RoundsCode.chain NJM_RoundJoin.R D pre rows carry) := by
 induction rows generalizing carry with
 | nil=>rfl
 | cons r rest ih=>
   rw [NJM_RoundsInvariant.cons_run]
   unfold chain
   rw [one_source native cut token frame D pre r carry]
   generalize run (S1SemanticCode.roundStep NJM_RoundJoin.R D pre carry.2.2 carry.2.1 carry.1 r)=head
   rcases head with ⟨log,reply⟩
   cases reply with
   | fail e=>rfl
   | div=>rfl
   | ok reply=>
     cases reply with
     | Err e=>simp only [NGX_RunBind.appendResult,NGX_CodeTrace.pure_run,List.append_nil]
     | Ok next=>
       simp only [NGX_RunBind.appendResult]
       rw [ih next]

/-- Final positive134 join. Native observations and their exact reviewed
cuts are the only non-input parameters; no operation dictionary/child law,
independent selected post, success, endpoint equation or run is assumed. -/
theorem rounds {H : Type} (native : NJM_RoundsCut.Observations) (cut : NJM_RoundsCut.Cut native)
 (token frame : Nat) (D : aspis_core.Digest32 H) (bytes : Slice U8)
 (pre : AspisR1PrefixAggregateParser.r1_wire.Prefix)
 (parsed : AspisR1PrefixAggregateParser.r1_wire.Prefix.parse bytes=ok (.Ok pre))
 (t : r1_wire.SemanticTranscript H) :
 ∃ running,
 run (S1SemanticCode.rounds NJM_RoundJoin.R D (PrefixAdapter.fromOld pre) t)=
 chain native token frame D (PrefixAdapter.fromOld pre) sites
  (running,Array.repeat 10#usize aspis_core.field.QM31.ZERO,t) := by
 obtain ⟨running,whole,initial⟩:=NJM_RoundsPacket.source D bytes pre parsed t
 refine ⟨running,?_⟩
 rw [source native cut token frame D (PrefixAdapter.fromOld pre) sites]
 exact whole.trans (NJM_RoundsJoin.source D bytes pre parsed sites _).symm

#print axioms one_source
#print axioms source
#print axioms rounds
end AspisR1.NJM_RoundsInduction
end
