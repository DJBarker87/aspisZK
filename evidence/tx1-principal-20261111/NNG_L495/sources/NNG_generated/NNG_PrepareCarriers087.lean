import NMP_Transport_T13
import LIBC_PreparedCarriers
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_PrepareCarriers087
open Aeneas Aeneas.Std NMP_Transport
open NMT_Transport (arr arr_inverse)

def wide (x : NMP_prepare.aspis_core.field.wide_exact.WideExact) :
    AspisR1PublicPreparation.aspis_core.field.WideExact := ⟨toT1 x.c0,toT1 x.c1⟩
def wideBack (x : AspisR1PublicPreparation.aspis_core.field.WideExact) :
    NMP_prepare.aspis_core.field.wide_exact.WideExact := ⟨fromT1 x.c0,fromT1 x.c1⟩
theorem wide_inverse (x : NMP_prepare.aspis_core.field.wide_exact.WideExact) : wideBack (wide x)=x := by
  cases x <;> simp only [wide,wideBack,toT1_inverse]
theorem wideBack_inverse (x : AspisR1PublicPreparation.aspis_core.field.WideExact) : wide (wideBack x)=x := by
  cases x <;> simp only [wide,wideBack,fromT1_inverse]
def variant : NMP_prepare.transport.Variant → AspisR1PublicPreparation.transport.Variant
 | .S1=>.S1 | .S2=>.S2 | .D=>.D
def variantBack : AspisR1PublicPreparation.transport.Variant → NMP_prepare.transport.Variant
 | .S1=>.S1 | .S2=>.S2 | .D=>.D
theorem variant_inverse (x : NMP_prepare.transport.Variant) : variantBack (variant x)=x := by cases x <;> rfl
theorem variantBack_inverse (x : AspisR1PublicPreparation.transport.Variant) : variant (variantBack x)=x := by cases x <;> rfl

def view (x : NMP_prepare.verifier.View) : AspisR1PublicPreparation.verifier.View :=
 ⟨variant x.variant,x.semantic,x.y1,wide x.inactive,x.round0,x.folded_root,x.round1,x.final_message,x.query_bytes⟩
def viewBack (x : AspisR1PublicPreparation.verifier.View) : NMP_prepare.verifier.View :=
 ⟨variantBack x.variant,x.semantic,x.y1,wideBack x.inactive,x.round0,x.folded_root,x.round1,x.final_message,x.query_bytes⟩
theorem view_inverse (x : NMP_prepare.verifier.View) : viewBack (view x)=x := by
 cases x <;> simp only [view,viewBack,variant_inverse,wide_inverse]
theorem viewBack_inverse (x : AspisR1PublicPreparation.verifier.View) : view (viewBack x)=x := by
 cases x <;> simp only [view,viewBack,variantBack_inverse,wideBack_inverse]

def prepared (x : NMP_prepare.verifier.Prepared) : AspisR1PublicPreparation.verifier.Prepared :=
 ⟨variant x.variant,x.roots,wide x.gamma,wide x.kappa,arr wide x.alpha,toT1 x.rho,x.queries,
  arr toT1 x.semantic_alpha,arr toT2 x.z,wide x.claim,x.state⟩
def preparedBack (x : AspisR1PublicPreparation.verifier.Prepared) : NMP_prepare.verifier.Prepared :=
 ⟨variantBack x.variant,x.roots,wideBack x.gamma,wideBack x.kappa,arr wideBack x.alpha,fromT1 x.rho,x.queries,
  arr fromT1 x.semantic_alpha,arr fromT2 x.z,wideBack x.claim,x.state⟩
theorem prepared_inverse (x : NMP_prepare.verifier.Prepared) : preparedBack (prepared x)=x := by
 cases x
 simp only [prepared,preparedBack,variant_inverse,wide_inverse,toT1_inverse]
 congr 1
 · exact arr_inverse wide wideBack wide_inverse _
 · exact arr_inverse toT1 fromT1 toT1_inverse _
 · exact arr_inverse toT2 fromT2 toT2_inverse _
theorem preparedBack_inverse (x : AspisR1PublicPreparation.verifier.Prepared) : prepared (preparedBack x)=x := by
 cases x
 simp only [prepared,preparedBack,variantBack_inverse,wideBack_inverse,fromT1_inverse]
 congr 1
 · exact arr_inverse wideBack wide wideBack_inverse _
 · exact arr_inverse fromT1 toT1 fromT1_inverse _
 · exact arr_inverse fromT2 toT2 fromT2_inverse _
#print axioms wide_inverse
#print axioms wideBack_inverse
#print axioms variant_inverse
#print axioms variantBack_inverse
#print axioms view_inverse
#print axioms viewBack_inverse
#print axioms prepared_inverse
#print axioms preparedBack_inverse
end AspisR1.NNG_PrepareCarriers087
