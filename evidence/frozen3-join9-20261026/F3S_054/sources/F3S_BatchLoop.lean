import Port9OR_BatchLoop
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3S_BatchLoop
open Aeneas Aeneas.Std Result AspisR1Stage2 CheckpointBytes5Effect
open Port9OR_BatchStep (Indices Values)
 theorem dictionary (base : Port3_NativeBatchBody.Ops) {Hash : Type}
    (D E : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (proof : Slice U8) (root : Array U8 32#usize) (tree lo n slot : Usize) (keys : Array U64 16#usize)
    (fuel : Nat) (idx : Indices) (val : Values) (d pos : Usize) :
    Port9OR_BatchLoop.code base D hash proof root tree lo n slot keys fuel idx val d pos=
      Port9OR_BatchLoop.code base E hash proof root tree lo n slot keys fuel idx val d pos := by
  induction fuel generalizing idx val d pos with
  | zero => rfl
  | succ fuel ih =>
    simp only [Port9OR_BatchLoop.code,Port9OR_BatchLoop.body_dictionary base D E]
    congr 1
    funext out
    cases out with
    | done result => rfl
    | cont next => exact ih next.1 next.2.1 next.2.2.1 next.2.2.2
#print axioms dictionary
end AspisR1.F3S_BatchLoop
end
