import LPq_PowersStep
import XRy_PowersLoop
set_option autoImplicit false
namespace AspisR1.LPq_Powers
open Aeneas Aeneas.Std Result ControlFlow LPi_FieldValues LPq_FieldPorts LPq_PowersStep XRo_Join_Carriers

theorem loop (fuel : Nat) {N : Usize} (x : NE) (hx : canonE x)
    (a : Array NE N) (p : NE) (hp : canonE p) (i : Usize)
    (hi : i.val≤N.val) (remaining : N.val-i.val≤fuel) :
    ∃ out, FIo_Native.weights.powers_loop x a p i=ok out ∧
      AspisR1LoopPowers.weights.early_powers_loop (port x) (arr port a) (port p) i=
        ok (arr port out) := by
  induction fuel generalizing a p i with
  | zero =>
    have hn : ¬i<N := by scalar_tac
    refine ⟨a,?_,?_⟩
    · apply XRy_PowersLoop.done
      simp only [FIo_Native.weights.powers_loop.body,if_neg hn]
    · apply XRy_PowersLoop.done
      simp only [AspisR1LoopPowers.weights.early_powers_loop.body,if_neg hn]
  | succ n ih =>
    by_cases hlt : i.val<N.val
    · obtain ⟨i',vi,cases⟩ := LPq_PowersStep.step x p a i hlt hx hp
      rcases cases with ⟨he,en,et⟩ | ⟨he,p',hp',en,et⟩
      · exact ⟨a.set i p,XRy_PowersLoop.done _ _ _ en,XRy_PowersLoop.done _ _ _ et⟩
      · obtain ⟨out,hr,ht⟩ := ih (a.set i p) p' hp' i' (by omega) (by omega)
        exact ⟨out,(XRy_PowersLoop.cont _ _ _ en).trans hr,
          (XRy_PowersLoop.cont _ _ _ et).trans ht⟩
    · have hn : ¬i<N := by scalar_tac
      refine ⟨a,?_,?_⟩
      · apply XRy_PowersLoop.done
        simp only [FIo_Native.weights.powers_loop.body,if_neg hn]
      · apply XRy_PowersLoop.done
        simp only [AspisR1LoopPowers.weights.early_powers_loop.body,if_neg hn]

def claim (x : NE) : AspisR1CurrentPreparedClaim.Concrete.E :=
  AspisR1ClaimPreparedBridge.toClaimE (wide x)

theorem one_canonical : canonE FIo_Native.aspis_core.field.wide_exact.WideExact.ONE := by
  norm_num [canonE,canonQ,canonC,LPi_CMProduct.Canon,
    FIo_Native.aspis_core.field.wide_exact.WideExact.ONE,
    FIo_Native.aspis_core.field.QM31.ONE,FIo_Native.aspis_core.field.QM31.ZERO]

theorem zero_port : port FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO=
    AspisR1LoopPowers.field.WideExact.ZERO := by
  unfold FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO FIo_Native.aspis_core.field.QM31.ZERO
    AspisR1LoopPowers.field.WideExact.ZERO AspisR1LoopPowers.field.QM31.ZERO
  rfl

theorem one_port : port FIo_Native.aspis_core.field.wide_exact.WideExact.ONE=
    AspisR1LoopPowers.field.WideExact.ONE := by
  unfold FIo_Native.aspis_core.field.wide_exact.WideExact.ONE FIo_Native.aspis_core.field.QM31.ONE
    FIo_Native.aspis_core.field.QM31.ZERO AspisR1LoopPowers.field.WideExact.ONE
    AspisR1LoopPowers.field.QM31.ONE AspisR1LoopPowers.field.QM31.ZERO
  rfl

theorem map_ports {N : Usize} (a : Array NE N) :
    AspisR1CurrentPreparedClaim.ClaimPowers.mapArray (arr port a)=arr claim a := by
  apply Subtype.ext
  change (a.val.map port).map AspisR1CurrentPreparedClaim.ClaimPowers.fromPowers=a.val.map claim
  rw [List.map_map]
  rfl

/-- Total native emitted powers and the concrete cohort powers, SAME returned
array with all eight words ported. Native seven-write evidence can identify this
unique carrier; no powers Result equality is an input hypothesis. -/
theorem source (N : Usize) (x : NE) (hx : canonE x) :
    ∃ out, FIo_Native.weights.powers N x=ok out ∧
      AspisR1CurrentPreparedClaim.ClaimPowers.powers N (claim x)=ok (arr claim out) := by
  obtain ⟨out,hn,ht⟩ := loop N.val x hx
    (Array.repeat N FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO)
    FIo_Native.aspis_core.field.wide_exact.WideExact.ONE one_canonical 0#usize
    (by scalar_tac) (by scalar_tac)
  refine ⟨out,hn,?_⟩
  have model : AspisR1LoopPowers.weights.early_powers N (port x)=ok (arr port out) := by
    simpa only [AspisR1LoopPowers.weights.early_powers,XRy_ArrayMap.repeated,zero_port,one_port] using ht
  unfold AspisR1CurrentPreparedClaim.ClaimPowers.powers
  have input : AspisR1CurrentPreparedClaim.ClaimPowers.toPowers (claim x)=port x := rfl
  rw [input,model,bind_tc_ok,map_ports]

#print axioms loop
#print axioms one_canonical
#print axioms zero_port
#print axioms one_port
#print axioms map_ports
#print axioms source
end AspisR1.LPq_Powers
