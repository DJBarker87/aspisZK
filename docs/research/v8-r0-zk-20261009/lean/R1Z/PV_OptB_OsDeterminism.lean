import R1Z.PV_OptB_Factorization
set_option autoImplicit false
namespace R1Z.PV_OptB_OsDeterminism
open PV_RunJoin_OsWorld PV_RunJoin_CallerWorld
variable {E File Reply Time Worker : Type}

/-- Exact request/reply/next-world determinism at a synchronized entered file
call, including arbitrary error replies. It does not prove synchronized entry. -/
theorem file_unique [DecidableEq File] (laws : Laws E File Reply Time Worker)
    (world : World E File Reply Time Worker) (request : Request File)
    (left right : Reply) (a b : World E File Reply Time Worker)
    (hl : FileAllowed laws world request left a) (hr : FileAllowed laws world request right b) :
    left = right ∧ a = b := by
  have same := Option.some.inj (hl.1.symm.trans hr.1)
  exact Prod.mk.inj same

/-- The full raw entropy reply retains both partial-write bytes and the
exact OS error. Again, this is at the same reached position only. -/
theorem entropy_unique (laws : Laws E File Reply Time Worker)
    (world : World E File Reply Time Worker) (i : Fin 128) (left right : RawReply E)
    (hl : EntropyAllowed laws world i left) (hr : EntropyAllowed laws world i right) :
    left = right := hl.2.1.symm.trans hr.2.1

#print axioms file_unique
#print axioms entropy_unique
end R1Z.PV_OptB_OsDeterminism
