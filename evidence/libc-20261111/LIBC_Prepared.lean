import LIBC_PreparedCarriers
import LIBC_PreparedDomain
import LIBC_CheckValuesDomain
import LIBC_SpecMap
set_option autoImplicit false
noncomputable section
namespace LIBC_Prepared
open RSL
/-- All operational content is concrete. The only bundle parameter contains
carrier type equalities, discharged by rfl when LIB_ assembles VLib. -/
def child (V : VLib) (t : LIBC_PreparedCarriers.Types V) : PreparedNew V :=
 {dom := fun a => LIBC_PreparedDomain.Domain (LIBC_PreparedCarriers.input t a)
  law := fun a => Spec.map (LIBC_PreparedCarriers.output t)
   (LIBC_PreparedLaw.law (LIBC_PreparedCarriers.input t a))}
def value {V : VLib} (t : LIBC_PreparedCarriers.Types V)
 (a : Verified V × V.View × V.E29) (env : Env) :=
 LIBC_PreparedCarriers.output t (LIBC_PreparedLaw.value (LIBC_PreparedCarriers.input t a) env)
theorem returns {V : VLib} (t : LIBC_PreparedCarriers.Types V)
 (a : Verified V × V.View × V.E29) (env : Env) :
 NND_Returned.Returns ((child V t).law a) env (value t a env) :=
 NND_Returned.map _ _ env _ (LIBC_PreparedLaw.returns _ env)
/-- Full graph plus exactly the CLOSED model's abort prefixes, transported
separately through the carrier map; no native Cut relation defines this law. -/
theorem exact_graph {V : VLib} (t : LIBC_PreparedCarriers.Types V)
 (a : Verified V × V.View × V.E29) (env : Env) (o : Obs (Except V.VErr V.Prepared × V.E29)) :
 (child V t).law a env o ↔ ∃ source,
 LIBC_PreparedLaw.law (LIBC_PreparedCarriers.input t a) env source ∧
 o = LIBC_SpecMap.observation (LIBC_PreparedCarriers.output t) source :=
 LIBC_SpecMap.exact _ _ env o
theorem caller_clauses {V : VLib} (t : LIBC_PreparedCarriers.Types V)
 (a : Verified V × V.View × V.E29) :
 (child V t).dom a ↔ LIBC_PreparedDomain.Domain (LIBC_PreparedCarriers.input t a) := Iff.rfl
theorem native_same_arguments {V : VLib} (t : LIBC_PreparedCarriers.Types V)
 (a : Verified V × V.View × V.E29) (env : Env) :
 (LIBC_PreparedLaw.run (LIBC_PreparedCarriers.input t a) env).2 =
 AspisR1.NGN_Emitted.prepared AspisR1.NHL_PreparedScalars.actual
 (LIBC_PreparedLog.digest env) (LIBC_PreparedCarriers.verified t a.1)
 (Eq.mp t.view a.2.1) () (Eq.mp t.e29 a.2.2) :=
 LIBC_PreparedLaw.native_result _ env
#print axioms returns
#print axioms exact_graph
#print axioms caller_clauses
#print axioms native_same_arguments
end LIBC_Prepared
