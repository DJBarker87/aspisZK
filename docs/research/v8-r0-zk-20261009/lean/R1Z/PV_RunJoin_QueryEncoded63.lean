import R1Z.PV_RunJoin_QueryWindow63
import R1Z.PV_RunJoin_PostBind63
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_QueryEncoded63
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_WeightInstalled46
open PV_RunJoin_ResultPost41
abbrev W := aspis_core.field.wide_exact.WideExact

def encode (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) (folded : Slice W) (q : Usize) : Result (alloc.vec.Vec U8) := do
  let values ← PV_RunJoin_QueryWindow63.window folded q
  @prover.encoded_slice (types base) (selected base heap box ops) values

theorem length (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) (folded : Slice W) (q : Usize) (bound : q.val<262144) :
    Post (fun out => out.length=128) (encode base heap box ops folded q) := by
  letI : ExternalTypes := types base
  unfold encode
  apply PV_RunJoin_PostBind63.guarded _ _ _ _ (PV_RunJoin_QueryWindow63.length folded q bound)
  intro values hvalues
  obtain ⟨out,hout,hval,hlen⟩ := PV_RunJoin_EncodedComplete41.encode ops values
    (by rw [hvalues];scalar_tac)
  rw [PV_RunJoin_EncodedInstalled48.complete base heap box ops,hout]
  change out.length=128
  rw [hlen,hvalues]

#print axioms encode
#print axioms length
end R1Z.PV_RunJoin_QueryEncoded63
