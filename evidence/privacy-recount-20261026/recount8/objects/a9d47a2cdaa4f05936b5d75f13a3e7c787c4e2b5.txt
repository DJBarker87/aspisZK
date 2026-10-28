import R1Z.PV_RunJoin_WorldProjection33
import R1Z.PV_RunJoin_ReachedSource33
import R1Z.PV_W_ReachedThreading
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_EntrySimulation33
open Aeneas Aeneas.Std ProverRwFull ProverRwRetryModel
open PV_W_Threading PV_W_Syntax PV_W_ReachedEffects PV_RunJoin_WorldProjection33
variable [ExternalTypes]
variable {W V C D : Type}

/-- Complete interpreted run of the actual emitted entry. Hash is an effectful
subprogram. The local complete-run laws remain P obligations to install for
the actual security-model interpreter; source erasure does not supply them. -/
theorem entry (world : W → V) (tag : C → D)
    (left : Interpreter Op W C Aeneas.Std.Error)
    (right : Interpreter Op V D Aeneas.Std.Error)
    (local_law : ∀ {B : Type} (op : Op B) w,
      project world tag (left op w) = right op (world w))
    (pub : Pub) (compiled : Compiled) (hash : PV_W_Callbacks.Hash)
    (secret : Secret) (store : Store) (w : W) :
    project world tag (eval left
      (PV_W_R_Entry.program pub compiled .S2 hash secret store) w) =
    eval right (PV_W_R_Entry.program pub compiled .S2 hash secret store) (world w) :=
  eval_project world tag left right local_law _ w

local instance : ProverRwRngCaller.NativeTypes := PV_RunJoin_CallerWorld.nativeTypes
local instance : ProverRwRngCaller.ErasureFns := ⟨fun _ value => .ok value,fun _ value => .ok value⟩
variable {N Client : Type}
/-- Same theorem at precisely the canonical-associated public and ORIGINAL
compiled payload. This is not a replacement payload or a changed failure event. -/
theorem associated (base : ExternalTypes)
    (ops : PV_RunJoin_NativeSelectedInputs.SourceState base N Client →
      @ExternalFuns (PDict_CodecDictionary.native base))
    (sourceHash : Slice (Slice U8) → Result (Array U8 32#usize))
    (i : PV_Src_NativeInput.Input)
    (s : PV_RunJoin_NativeSelectedInputs.SourceState base N Client) :
    letI : ExternalTypes := PDict_CodecDictionary.native base
    let d := PV_RunJoin_NativeSelectedInputs.inputs base ops sourceHash i
    ∀ (world : W → V) (tag : C → D)
      (left : Interpreter Op W C Aeneas.Std.Error)
      (right : Interpreter Op V D Aeneas.Std.Error),
      (∀ {B : Type} (op : Op B) w,
        project world tag (left op w) = right op (world w)) →
      ∀ (hash : PV_W_Callbacks.Hash) (secret : Secret) (w : W),
      project world tag (eval left
        (PV_W_R_Entry.program (d.pub s) (d.compiled s) .S2 hash secret s.ledger) w) =
      eval right (PV_W_R_Entry.program (d.pub s) (d.compiled s) .S2 hash secret s.ledger) (world w) := by
  letI : ExternalTypes := PDict_CodecDictionary.native base
  dsimp only
  intro world tag left right local_law hash secret w
  exact entry world tag left right local_law _ _ hash secret _ w

#print axioms entry
#print axioms associated
end R1Z.PV_RunJoin_EntrySimulation33
