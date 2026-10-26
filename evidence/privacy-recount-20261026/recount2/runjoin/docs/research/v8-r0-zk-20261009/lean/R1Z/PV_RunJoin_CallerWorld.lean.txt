import R1Z.PV_RunJoin_World
import R1Z.ProverRwRngCallerEvents
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CallerWorld
open Aeneas Aeneas.Std Result
open ProverRwRngCaller
open R1Z.ProverRwRngCallerControl R1Z.ProverRwRngCallerReplay
variable [NativeTypes] [ErasureFns] {E : Type}

/-- Finite native-error representation; value-level only, with its ABI/source
association still unproved. No enumeration of this carrier is evaluated. -/
@[reducible] def nativeTypes : NativeTypes := ⟨Unit,fun _ _ => Fin (2^32-1)⟩

abbrev RawReply (E : Type) := (Fin 64 → PV_RunJoin_World.Byte) × Option E
abbrev RawTape (E : Type) := Fin 128 → RawReply E
abbrev Sample (E N L B O : Type) := RawTape E × N × L × B × O

def reply (osError : E → getrandom.error.Error)
    (raw : RawReply E) :
    (Array U8 64#usize) × core.result.Result Unit getrandom.error.Error :=
  ((PV_RunJoin_World.reply (raw.1,none)).1,
    match raw.2 with | none => .Ok () | some e => .Err (osError e))

def provider (osError : E → getrandom.error.Error)
    (raw : RawTape E) : Tape :=
  ⟨⟨List.ofFn (fun i => reply osError (raw i)),by simp only [List.length_ofFn]; scalar_tac⟩,0#usize⟩

def initial {N L B O : Type} (osError : E → getrandom.error.Error)
    (s : Sample E N L B O) : State N L B :=
  (provider osError s.1,s.2.1,s.2.2.1,s.2.2.2.1,0#usize)

def execute {N L B O : Type} (osError : E → getrandom.error.Error)
    (policy : Policy N) (body : Body B L) (s : Sample E N L B O) : Result (Output N L B) :=
  prove_masked_retrying_with policy body true (provider osError s.1) s.2.1 s.2.2.1 s.2.2.2.1

instance finite [Fintype E] {N L B O : Type} [Fintype N] [Fintype L] [Fintype B] [Fintype O] :
    Fintype (Sample E N L B O) := inferInstance
instance nonempty [Nonempty E] {N L B O : Type} [Nonempty N] [Nonempty L] [Nonempty B] [Nonempty O] :
    Nonempty (Sample E N L B O) := inferInstance

theorem capacity (osError : E → getrandom.error.Error)
    (raw : RawTape E) :
    (provider osError raw).used.val = 0 ∧ (provider osError raw).replies.val.length = 128 := by
  constructor
  · rfl
  · simp only [provider,List.length_ofFn]

theorem replay {N L B O : Type} (osError : E → getrandom.error.Error)
    (policy : Policy N) (body : Body B L) (s : Sample E N L B O) (out : Output N L B)
    (admitted : execute osError policy body s = .ok out) :
    ∃ states, Replay policy body (initial osError s) states out ∧ callbacks states ≤ 8 :=
  cap8 policy body _ _ _ _ out admitted

#print axioms reply
#print axioms provider
#print axioms execute
#print axioms finite
#print axioms nonempty
#print axioms capacity
#print axioms replay
end R1Z.PV_RunJoin_CallerWorld
