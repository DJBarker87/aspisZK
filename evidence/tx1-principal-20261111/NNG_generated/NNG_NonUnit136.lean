import NNG_EmittedContext
set_option autoImplicit false
namespace AspisR1.NNG_NonUnit136
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted

theorem nonUnit {A : Type} (x y : A) (different : x≠y) : A≠Unit := by
  intro h
  subst A
  exact different (Subsingleton.elim x y)
#print axioms nonUnit

theorem wireResult (A : Type) : core.result.Result A r1_wire.Error ≠ Unit :=
  nonUnit (core.result.Result.Err r1_wire.Error.Public : core.result.Result A r1_wire.Error) (.Err .InvalidRow) (by intro h;cases h)
#print axioms wireResult

theorem terminalResult : core.result.Result Q aspis_core.state_only_prefix.r0.Error ≠ Unit :=
  nonUnit (core.result.Result.Err aspis_core.state_only_prefix.r0.Error.Public : core.result.Result Q aspis_core.state_only_prefix.r0.Error) (.Err .InvalidRow) (by intro h;cases h)
#print axioms terminalResult

theorem circleReply (t : r1_wire.SemanticTranscript Unit) :
    (core.result.Result aspis_core.circle.SecureCirclePoint r1_wire.Error × r1_wire.SemanticTranscript Unit) ≠ Unit :=
  nonUnit ((core.result.Result.Err r1_wire.Error.Public,t) : core.result.Result aspis_core.circle.SecureCirclePoint r1_wire.Error × r1_wire.SemanticTranscript Unit) (.Err .InvalidRow,t) (by intro h;cases h)
#print axioms circleReply

theorem scalar : Q≠Unit := by
  let zero : Q := ⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩
  let one : Q := ⟨⟨1#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩
  apply nonUnit zero one
  intro same
  have values := congrArg (fun q : Q => q.c0.a.val) same
  have impossible : (0 : Nat)=1 := values
  cases impossible
#print axioms scalar

theorem state : (Array U8 32#usize)≠Unit := by
  let zero : Array U8 32#usize := Array.repeat 32#usize 0#u8
  let one : Array U8 32#usize := Array.repeat 32#usize 1#u8
  apply nonUnit zero one
  intro same
  have values := congrArg (fun a : Array U8 32#usize => a.val.head?) same
  have impossible : (some (0#u8) : Option U8)=some 1#u8 := values
  have words := congrArg (fun x : U8 => x.val) (Option.some.inj impossible)
  have impossible : (0 : Nat)=1 := words
  cases impossible
#print axioms state
end AspisR1.NNG_NonUnit136
