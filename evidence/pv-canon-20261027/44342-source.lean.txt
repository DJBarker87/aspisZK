import R1Z.PV_Canon_Round
import R1Z.PV_Canon_CheckedRounds
import R1Z.PV_Canon_RoundCounter
import R1Z.PV_Canon_RoundsGeneric
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Canon
open Aeneas Aeneas.Std Result ProverRwFull
 theorem rounds_checked (base : ExternalTypes)
    (ops : @ExternalFuns (PV_Join_PublicCaller.native base))
    {H F : Type} (digest : aspis_core.digest.Digest32 H) (oracleInst : host_sumcheck.Oracle F)
    (n : Nat) (s : host_wire.SemanticTranscript H) (output : alloc.vec.Vec U8)
    (point : Array aspis_core.field.QM31 10#usize) (running : aspis_core.field.QM31)
    (round : Usize) (oracle : F) (hn : round.val+n=10) :
    @host_sumcheck.prove_sumcheck_rounds (PV_Join_PublicCaller.native base)
      (PV_Join_PublicCaller.selected base ops) H F digest oracleInst s output point running round oracle =
    @checked_rounds (PV_Join_PublicCaller.native base)
      (PV_Join_PublicCaller.selected base ops) H F digest oracleInst s output point running round oracle := by
  exact rounds_generic (PV_Join_PublicCaller.selected base ops) digest oracleInst
    (fun s output point running round oracle hr =>
      round_checked base ops digest oracleInst s output point running round oracle hr)
    n s output point running round oracle hn
#print axioms rounds_checked
end R1Z.PV_Canon
