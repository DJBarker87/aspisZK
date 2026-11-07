import LIB_VLib
import LIBC_Prepared
import LIBC_PreparedR4
set_option autoImplicit false
noncomputable section
namespace LIB_Prepared
open RSL
/-- Only representation equalities; every one is definitional in actual VL-star. -/
def types : LIBC_PreparedCarriers.Types LIB_VLib.library where
 challenges := rfl
 alpha := rfl
 claims := rfl
 k29 := rfl
 point := rfl
 transcript := rfl
 view := rfl
 prepared := rfl
 e29 := rfl
 error := rfl
def child : PreparedNew LIB_VLib.library := LIBC_Prepared.child LIB_VLib.library types
abbrev value := LIBC_Prepared.value types
abbrev input := LIBC_PreparedCarriers.input types
abbrev output := LIBC_PreparedCarriers.output types
theorem types_exact : types = ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := rfl
theorem child_exact : child = LIBC_Prepared.child LIB_VLib.library types := rfl
theorem returns (a : Verified LIB_VLib.library × LIB_VLib.library.View × LIB_VLib.library.E29) (env : Env) :
 NND_Returned.Returns (child.law a) env (value a env) := LIBC_Prepared.returns types a env
theorem exact_graph (a : Verified LIB_VLib.library × LIB_VLib.library.View × LIB_VLib.library.E29)
 (env : Env) (o : Obs (Except LIB_VLib.library.VErr LIB_VLib.library.Prepared × LIB_VLib.library.E29)) :
 child.law a env o ↔ ∃ source,
 LIBC_PreparedLaw.law (input a) env source ∧ o = LIBC_SpecMap.observation output source :=
 LIBC_Prepared.exact_graph types a env o
theorem caller_clauses (a : Verified LIB_VLib.library × LIB_VLib.library.View × LIB_VLib.library.E29) :
 child.dom a ↔ LIBC_PreparedDomain.Domain (input a) := Iff.rfl
#print axioms types_exact
#print axioms child_exact
#print axioms returns
#print axioms exact_graph
#print axioms caller_clauses
end LIB_Prepared
