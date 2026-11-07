import NLQ_CheckpointRead
import NFU_ZeroPort
set_option autoImplicit false
noncomputable section
namespace NLQ_ZeroSite
open Aeneas Aeneas.Std Result AspisR1 AspisR1.S2W_D189Entry
/-- Install CLOSED342 at its SAME checkpoint-data occurrence, deriving its
numeric extent clause. Native immutable-carrier/ABI association is still the
parent cut's obligation; this helper introduces no all-zero premise. -/
theorem source (e : Entry) (ops : AdapterRw.Ops) (bytes : Slice U8)
 (read : AdapterRw.r1_pool_adapter.owned.OwnedAccount.data ops (e.snapshot 2 1768 1768)=.ok (.Ok bytes)) :
 AdapterRw.r1_pool_adapter.owned.require_zero bytes=
 (do let result ← NFQ_ScanReference.zero_ref bytes
     ok (NFQ_ZeroSource.result result)) :=
 NFU_ZeroPort.source bytes (NLQ_CheckpointRead.at_site e ops bytes read).2.2
#print source
#print axioms source
end NLQ_ZeroSite
