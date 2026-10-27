import R1Z.PV_RunJoin_OsWorld
set_option autoImplicit false
namespace R1Z.PV_RunJoin_NativeEffectInterface
open Aeneas Aeneas.Std
open PV_RunJoin_OsWorld
variable {E File Reply Time Worker : Type}

/-- Native operations and complete effect observations are explicit DATA.
Supplying these functions is not a proof they interpret the frozen binary. -/
structure Native (E File Reply Time Worker : Type) where
  entropyDraw : World E File Reply Time Worker → Fin 128 →
    PV_RunJoin_CallerWorld.RawReply E → Prop
  open64 : World E File Reply Time Worker → List U8 → U32 → U32 → Reply → Prop
  read : World E File Reply Time Worker → File → Usize → Reply → Prop
  write : World E File Reply Time Worker → File → List U8 → Reply → Prop
  sync : World E File Reply Time Worker → File → Reply → Prop
  close : World E File Reply Time Worker → File → Reply → Prop
  time : World E File Reply Time Worker → Time → Prop
  worker : World E File Reply Time Worker → Worker → Prop

variable [DecidableEq File]

/-- Exact identity obligations for matching a native interpreter to the named
world fields. These are quantified propositions, never axioms or availability
assertions; in particular no successful entropy outcome is required. -/
structure Identity (native : Native E File Reply Time Worker)
    (laws : Laws E File Reply Time Worker) : Prop where
  entropy : ∀ world i reply, native.entropyDraw world i reply ↔
    EntropyAllowed laws world i reply
  open64 : ∀ world path flags mode reply next,
    fileStep (.open64 path flags mode) world = some (reply,next) →
    (native.open64 world path flags mode reply ↔ laws.open64 world path flags mode reply)
  read : ∀ world owner count reply next,
    fileStep (.read owner count) world = some (reply,next) →
    (native.read world owner count reply ↔ laws.read world owner count reply)
  write : ∀ world owner bytes reply next,
    fileStep (.write owner bytes) world = some (reply,next) →
    (native.write world owner bytes reply ↔ laws.write world owner bytes reply)
  sync : ∀ world owner reply next,
    fileStep (.sync owner) world = some (reply,next) →
    (native.sync world owner reply ↔ laws.sync world owner reply)
  close : ∀ world owner reply next,
    fileStep (.close owner) world = some (reply,next) →
    (native.close world owner reply ↔ laws.close world owner reply)
  time : ∀ world outcome next, timeStep world = some (outcome,next) →
    (native.time world outcome ↔ laws.time world outcome)
  worker : ∀ world outcome next, workerStep world = some (outcome,next) →
    (native.worker world outcome ↔ laws.worker world outcome)

#print Identity
end R1Z.PV_RunJoin_NativeEffectInterface
