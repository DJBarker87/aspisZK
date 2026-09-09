import EarlyC1Identification
import EarlyC1InstanceTransport

/-! Transport the numerical margin across the actual Fintype instances.
The preceding type diagnostic showed that the source optional object uses
a SimplexCategory-derived Fin instance, while the arithmetic leaf uses
Fin.fintype. Neither enumeration is unfolded here. -/
set_option autoImplicit false
set_option maxRecDepth 80
set_option maxHeartbeats 2000
namespace AspisV8.EarlyC1Specialization
open AspisV8.EarlyC1Projection AspisV8.EarlyC1Identification

noncomputable def explicit_instance : Fintype (Fin 262144) :=
  SimplexCategory.instFintypeToTypeOrderHomFinHAddNatLenOfNat
    (SimplexCategory.mk 262143)

noncomputable def before_margin :=
  @AspisV8.EarlyC1InstanceTransport.transport (Fin 262144)
    explicit_instance (Fin.fintype 262144) 245609 256

noncomputable def source_margin := before_margin c1_margin

/-- A qualifying late tuple identifies the unchanged optional object defined
from received C1 alone. The support premise is not an acceptance theorem. -/
theorem identify (received : C1Received) (p : C1Messages)
    (own : 245609 ≤ (support fibreEncode (receivedFibres received) p).card) :
    earlyC1 received = some p :=
  @early_eq_of_large_support (Fin 262144)
    (Fin 4 → AspisV5ComponentCQM31TowerExact.QM31Exact) Message (Fin 26)
    explicit_instance fibreEncode (receivedFibres received) p 245609 256
    exact_agreement_cap source_margin own

set_option pp.all true in
#print explicit_instance
set_option pp.all true in
#print before_margin
set_option pp.all true in
#print source_margin
#print axioms before_margin
#print axioms source_margin
#print axioms identify

end AspisV8.EarlyC1Specialization
