import LIB_Prepared
import LIB_S1
import LIB_Deployed
import TAS_Interfaces
set_option autoImplicit false
noncomputable section
namespace LIB_Instances
open RSL
/-- TX1 portion of the final bundle. TX2 L/V0/weak-law registration awaits LIBB_. -/
abbrev VL := LIB_VLib.library
abbrev P : PreparedNew VL := LIB_Prepared.child
abbrev C : TX1_345.S1Lib VL := LIB_S1.library
abbrev D : DeployedIds := LIB_Deployed.deployed
structure TX1Bundle where
 verifier : VLib
 prepared : PreparedNew verifier
 statement : TX1_345.S1Lib verifier
def tx1 : TX1Bundle := ⟨VL,P,C⟩
theorem verifier_exact : tx1.verifier = VL := rfl
theorem prepared_exact : tx1.prepared = P := rfl
theorem statement_exact : tx1.statement = C := rfl
#print axioms verifier_exact
#print axioms prepared_exact
#print axioms statement_exact
/-- Extract a projection's result type without postulating a value of its structure. -/
def resultType {A : Sort _} {B : Sort _} (_ : A → B) := B
section TASChecks
variable (S : TAS.Sig) (L : PoolLib) (V0 : TX2_241.V2Lib) (I : TAS.Impl L V0 VL)
/-- Exact TAS TX1 field types; these are type identities, not row candidates. -/
theorem tas136 : TX1_136.RowSpec_136 VL I.f136 =
 resultType (fun r : TAS.NMO_Root L V0 VL I => r.r136) := rfl
theorem tas137 : (TX1_136.RowSpec_136 VL I.f136 → TX1_137.RowSpec_137 VL I.f137) =
 resultType (fun r : TAS.NMP_Roots L V0 VL P I => r.r137) := rfl
theorem tas087 : (TX1_137.RowSpec_137 VL I.f137 → TX1_087.RowSpec_087 VL P I.f087) =
 resultType (fun r : TAS.NMP_Roots L V0 VL P I => r.r087) := rfl
theorem tas094 : (TX1_087.RowSpec_087 VL P I.f087 → TX1_094.RowSpec_094 VL P I.f094) =
 resultType (fun r : TAS.NMT_Roots L V0 VL P C I => r.r094) := rfl
theorem tas328 : (TX1_094.RowSpec_094 VL P I.f094 → TX1_328.RowSpec_328 VL P I.f328) =
 resultType (fun r : TAS.NMT_Roots L V0 VL P C I => r.r328) := rfl
theorem tas345 : (TX1_328.RowSpec_328 VL P I.f328 → TX1_345.RowSpec_345 VL P C I.f345) =
 resultType (fun r : TAS.NMT_Roots L V0 VL P C I => r.r345) := rfl
end TASChecks
#print axioms tas136
#print axioms tas137
#print axioms tas087
#print axioms tas094
#print axioms tas328
#print axioms tas345
end LIB_Instances
