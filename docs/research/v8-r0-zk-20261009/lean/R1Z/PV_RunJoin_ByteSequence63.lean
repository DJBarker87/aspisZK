import R1Z.PV_RunJoin_ByteScript63
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_ByteSequence63
open Aeneas Aeneas.Std Result PV_RunJoin_ByteScript63

def append : Code → Code → Code
  | .done,right => right
  | .read r next,right => .read r (fun a => append (next a) right)
  | .append s next,right => .append s (append next right)

theorem run (left right : Code) (out : alloc.vec.Vec U8) :
    PV_RunJoin_ByteScript63.run (append left right) out=
      (do let next ← PV_RunJoin_ByteScript63.run left out
          PV_RunJoin_ByteScript63.run right next) := by
  induction left generalizing out with
  | done => rfl
  | @read T r next ih =>
    simp only [append,PV_RunJoin_ByteScript63.run,ih,bind_assoc_eq]
  | append s next ih =>
    simp only [append,PV_RunJoin_ByteScript63.run,ih,bind_assoc_eq]

#print axioms append
#print axioms run
end R1Z.PV_RunJoin_ByteSequence63
