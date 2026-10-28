import NDO_JGa_Map
import RPv_JFy_PreparedSteps
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGb_PreparedMap
open Aeneas Aeneas.Std Result WP FIq_Native
open FIv_NativeValue (Canon)
open FIv_PreparedNew (NP)
open FIw_ArrayValue (canonical)

theorem source {N : Usize} (a : Array field.QM31 N) (hc : canonical a) :
    ∃ out,FIq_Native.core.array.Array.map (BuiltinFnMut field.QM31 NP) a field.PreparedQm31Multiplier.new=ok out ∧
      ∀ p∈out.val,JFy_PreparedSteps.Valid p := by
  apply JGa_Map.source
  intro x hx
  obtain ⟨p,hp,hpc⟩ := WP.spec_imp_exists (JFy_PreparedSteps.new x (hc x hx))
  exact ⟨p,by change (do let p ← field.PreparedQm31Multiplier.new x;ok (p,field.PreparedQm31Multiplier.new))=_;rw [hp,bind_tc_ok],hpc⟩
#print axioms source
end AspisR1.JGb_PreparedMap
end
