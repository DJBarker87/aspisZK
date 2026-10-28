import R1Z.PV_RunJoin_NativePublicReservation
import R1Z.PV_RunJoin_Deployed
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_InstalledFamily
open Aeneas Aeneas.Std Result ProverRwFull
open R0P R0Z R0Z.JointView R0Z.FsStatement R1Z.GamesR1
local notation "K" => PrivacyR1AcctBasis.K
local instance : ProverRwRngCaller.NativeTypes := PV_RunJoin_CallerWorld.nativeTypes
local instance : ProverRwRngCaller.ErasureFns := ⟨fun _ value => .ok value,fun _ value => .ok value⟩
variable {CommitHandle N C : Type}

/-- The missing selection is explicit. No successful compiler call, admission,
or relation to the endpoint witness is hidden in this data carrier. -/
structure Selection (CommitHandle : Type) where
  selected : (h : HonestProver K) → Statement K CommitHandle → h.Instance → PV_Src_NativeInput.Input
  publicRecord : Statement K CommitHandle → PV_Src_NativeInput.Input

def PublicBinding (selection : Selection CommitHandle) : Prop :=
  ∀ h x w, h.public w = x.1 →
    PV_Src_NativeInput.publicInput (selection.selected h x w) =
      PV_Src_NativeInput.publicInput (selection.publicRecord x)

def inputs (base : ExternalTypes)
    (ops : PV_RunJoin_NativeSelectedInputs.LedgerState base N C → @ExternalFuns (PDict_CodecDictionary.native base))
    (hash : Statement K CommitHandle → Slice (Slice U8) → Result (Array U8 32#usize))
    (selection : Selection CommitHandle) (h : HonestProver K)
    (x : Statement K CommitHandle) (w : h.Instance) :=
  PV_RunJoin_NativeSelectedInputs.ledgerInputs base ops (hash x) (selection.selected h x w)

def common (base : ExternalTypes)
    (ops : PV_RunJoin_NativeSelectedInputs.LedgerState base N C → @ExternalFuns (PDict_CodecDictionary.native base))
    (hash : Statement K CommitHandle → Slice (Slice U8) → Result (Array U8 32#usize))
    (selection : Selection CommitHandle) (x : Statement K CommitHandle) :=
  PV_RunJoin_NativeSelectedInputs.ledgerInputs base ops (hash x) (selection.publicRecord x)

theorem public_common (base : ExternalTypes)
    (ops : PV_RunJoin_NativeSelectedInputs.LedgerState base N C → @ExternalFuns (PDict_CodecDictionary.native base))
    (hash : Statement K CommitHandle → Slice (Slice U8) → Result (Array U8 32#usize))
    (selection : Selection CommitHandle) (binding : PublicBinding selection)
    (h : HonestProver K) (x : Statement K CommitHandle) (w : h.Instance) (hw : h.public w = x.1)
    (s : PV_RunJoin_NativeSelectedInputs.LedgerState base N C) :
    letI : ExternalTypes := PDict_CodecDictionary.native base
    (inputs base ops hash selection h x w).ops s = (common base ops hash selection x).ops s ∧
    (inputs base ops hash selection h x w).pub s = (common base ops hash selection x).pub s ∧
    (inputs base ops hash selection h x w).hash s = (common base ops hash selection x).hash s := by
  letI : ExternalTypes := PDict_CodecDictionary.native base
  exact ⟨rfl,PV_RunJoin_NativePublicReservation.public_eq base _ _ (binding h x w hw),rfl⟩

theorem map_error (base : ExternalTypes)
    (ops : PV_RunJoin_NativeSelectedInputs.LedgerState base N C → @ExternalFuns (PDict_CodecDictionary.native base))
    (hash : Statement K CommitHandle → Slice (Slice U8) → Result (Array U8 32#usize))
    (selection : Selection CommitHandle) (h : HonestProver K)
    (x : Statement K CommitHandle) (w : h.Instance)
    (s : PV_RunJoin_NativeSelectedInputs.LedgerState base N C) :
    letI : ExternalTypes := PDict_CodecDictionary.native base
    PV_RunJoin_MapErrInstalled.Identity ((inputs base ops hash selection h x w).ops s) :=
  PV_RunJoin_DictionaryIdentity.map_error base (ops s)

#print Selection
#print PublicBinding
#print axioms public_common
#print axioms map_error
end R1Z.PV_RunJoin_InstalledFamily
