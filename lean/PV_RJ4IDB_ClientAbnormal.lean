import PV_RJ4IDB_ClientTrace
set_option autoImplicit false
namespace PV_RJ4IDB
open Aeneas Aeneas.Std R1Z.ProverCommitRetry34
variable {H S P : Type}
theorem abort_preserved (expose : H → List (Bytes × Bytes))
 (o : PV_DIAG3.ClientHandlers H S P) (s t : H) (es : List PV_DIAG3.Event)
 (c : PV_DIAG3.Crash) :
 observedClient expose (fun _ => ⟨es,t,.abort c⟩) o s =
 decoder (diagWithState expose (⟨es,t,.abort c⟩ : PV_DIAG3.Execution H Nat)) := rfl

theorem divergence_preserved (expose : H → List (Bytes × Bytes))
 (o : PV_DIAG3.ClientHandlers H S P) (s t : H) (es : List PV_DIAG3.Event) :
 observedClient expose (fun _ => ⟨es,t,.diverge⟩) o s =
 decoder (diagWithState expose (⟨es,t,.diverge⟩ : PV_DIAG3.Execution H Nat)) := rfl

theorem panic_preserved (expose : H → List (Bytes × Bytes))
 (o : PV_DIAG3.ClientHandlers H S P) (s t : H) (es : List PV_DIAG3.Event)
 (p : PV_DIAG3.Panic) :
 observedClient expose (fun _ => ⟨es,t,.panic p⟩) o s =
 decoder (diagWithState expose (⟨es,t,.panic p⟩ : PV_DIAG3.Execution H Nat)) := rfl

/-- Model failure and divergence are handed to their explicit native handlers;
no canonical error text, empty history or termination is imposed on them. -/
theorem failed_handler (o : PV_DIAG3.ClientHandlers H S P) (e : Aeneas.Std.Error) :
 PV_DIAG3.clientAfter o (.fail e) = o.runtime e := rfl

theorem divergent_handler (o : PV_DIAG3.ClientHandlers H S P) :
 PV_DIAG3.clientAfter o .div = o.divergence := rfl
#print axioms abort_preserved
#print axioms divergence_preserved
#print axioms panic_preserved
#print axioms failed_handler
#print axioms divergent_handler
end PV_RJ4IDB
