import SdkC_Oracle
import Port9OR_Code
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3N_ProgramCarrier
open Aeneas Aeneas.Std Result AspisR1Stage2

theorem total {A Hash : Type} (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (total : ∀ parts,∃ digest,D.digest hash parts=ok digest) (c : SdkC_Source.Code A) :
    SdkC_Oracle.program c=Port9OR_Code.program D hash c := by
  induction c with
  | done a => rfl
  | step r next ih =>
    cases r <;> simp only [SdkC_Oracle.program,Port9OR_Code.program,VTop_OracleCode.continueWith]
    exact ih _
  | read parts next ih =>
    obtain ⟨digest,called⟩ := total parts
    simp only [SdkC_Oracle.program,Port9OR_Code.program,called]
    congr 1
    funext reply
    exact ih _

#print axioms total
end AspisR1.F3N_ProgramCarrier
end
