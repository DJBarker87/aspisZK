import RPu_FIv_Arithmetic
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIx_ArithmeticTotal
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ qm)
open FIv_NativeValue (Canon decode)

theorem map_success {A B : Type} (f : A → B) (r : Result A) (b : B)
    (run : FIv_Map.map f r=ok b) : ∃ a,r=ok a ∧ f a=b := by
  cases r with
  | ok a => exact ⟨a,rfl,Result.ok.inj run⟩
  | fail e => cases run
  | div => cases run

theorem add (x y : NQ) (hx : Canon x) (hy : Canon y) :
    ∃ out,FIq_Native.field.QM31.add x y=ok out ∧ Canon out ∧ decode out=decode x+decode y := by
  obtain ⟨out,hr,hc,hv⟩ := ExtractedMaskQM31Exact.current_qm_add_exact (qm x) (qm y) hx hy
  obtain ⟨native,hn,he⟩ := map_success qm _ out ((FIv_NativeQM.add x y).trans hr)
  exact ⟨native,hn,by simpa only [Canon,he] using hc,by simpa only [decode,he] using hv⟩

theorem mul (x y : NQ) (hx : Canon x) (hy : Canon y) :
    ∃ out,FIq_Native.field.QM31.mul x y=ok out ∧ Canon out ∧ decode out=decode x*decode y := by
  obtain ⟨out,hr,hc,hv⟩ := ExtractedMaskQM31Exact.current_qm_mul_exact (qm x) (qm y) hx hy
  obtain ⟨native,hn,he⟩ := map_success qm _ out ((FIv_NativeQM.mul x y).trans hr)
  exact ⟨native,hn,by simpa only [Canon,he] using hc,by simpa only [decode,he] using hv⟩
#print axioms map_success
#print axioms add
#print axioms mul
end AspisR1.FIx_ArithmeticTotal
end
