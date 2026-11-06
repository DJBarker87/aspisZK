import NLL_Tx2Caller
set_option autoImplicit false
noncomputable section
namespace NLL_Tx2AtActual
open Aeneas Aeneas.Std Result VTop_Stages AspisR1 NJU_CommonObserved

/-- The actual C04 source occurrence supplies its own SAME Prepared query
domain. This installs no independent successful-child premise at a root. -/
theorem source (wr rr : NP6_StdModel.Reservation) (merkle : Merkle) (finish : Finish)
 {X : Type} (d : aspis_core.digest.Digest32 X) (pub proof ck : Slice U8) (hash : X)
 (enteredProof : Slice U8) (p : verifier.Prepared) (folded : Array U8 32#usize)
 (reply : R Unit)
 (entered : Event.merkle enteredProof p folded reply∈(run wr rr merkle finish d pub proof ck hash none).events) :
 enteredProof=proof ∧ ∃ a,NJJ_Common.resume wr d ck proof pub .S2 hash=ok (.Ok (p,a)) ∧
 ∀ j,j<22 → p.queries.val[j]!.val<262144 :=
 NLL_Tx2Caller.source wr rr merkle finish d pub proof ck hash _ entered

set_option pp.proofs false
#print source
#print axioms source
end NLL_Tx2AtActual
end
