import FIv_Arithmetic
import EqualityValueAdapter
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIv_SubMap
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic
open FIv_NativeValue (Canon decode K)
open FIv_Map (map map_bind map_ok)
theorem mapped (x y : NQ) : map qm (FIq_Native.field.QM31.sub x y)=
    AspisR1SelectedMaskProbe.field.QM31.sub (qm x) (qm y) := by
  simp only [FIq_Native.field.QM31.sub,AspisR1SelectedMaskProbe.field.QM31.sub,qm,
    ← FIv_NativeCM.sub,bind_map,map_bind,map_ok]
theorem qm (x y z : NQ) (hx : Canon x) (hy : Canon y)
    (run : FIq_Native.field.QM31.sub x y=ok z) :
    Canon z ∧ decode z=decode x-decode y := by
  obtain ⟨r,returned,canon,value⟩ := EqualityValueAdapter.current_qm_sub_exact
    (FIv_NativeArithmetic.qm x) (FIv_NativeArithmetic.qm y) hx hy
  have transported := mapped x y
  rw [run,map_ok,returned] at transported
  have same := Result.ok.inj transported
  rw [← same] at canon value
  exact ⟨canon,value⟩
#print axioms mapped
#print axioms qm
end AspisR1.FIv_SubMap
end
