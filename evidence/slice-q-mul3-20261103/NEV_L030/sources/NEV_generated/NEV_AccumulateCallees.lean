import NEV_AccumulateRaw.FunsExternal
import NEV_AccumulateCarriers
import NEV_CodeFieldBridge
set_option autoImplicit false
noncomputable section
namespace NEV_AccumulateCallees
open Aeneas Aeneas.Std Result NEV_AccumulateCarriers
open NEV_AccumulateRaw.NEV_Bindings

def toCtorE (e : RawE) : NEV_CodeFieldRaw.aspis_core.field.wide_exact.WideExact :=
 ⟨⟨⟨e.c0.c0.a,e.c0.c0.b⟩,⟨e.c0.c1.a,e.c0.c1.b⟩⟩,
  ⟨⟨e.c1.c0.a,e.c1.c0.b⟩,⟨e.c1.c1.a,e.c1.c1.b⟩⟩⟩
def toPushBW (b : NEV_AccumulateRaw.BatchedWeights) : NEI_PushRaw.BatchedWeights :=
 ⟨b.raw,b.terms⟩

theorem native_e_reverse (x : FIo_Native.aspis_core.field.wide_exact.WideExact) :
    toNativeE (fromNativeE x)=x := by cases x;rfl
theorem native_q_reverse (x : FIo_Native.aspis_core.field.QM31) :
    toNativeQ (fromNativeQ x)=x := by cases x;rfl
theorem ctor_e_reverse (x : NEV_CodeFieldRaw.aspis_core.field.wide_exact.WideExact) :
    toCtorE (fromCtorE x)=x := by cases x;rfl

/-- These new laws transport only nominal raw extraction records. Each RHS
is the CLOSED concrete callee, with errors/divergence preserved, never an
assumed result or a supplied arithmetic equality. -/
theorem wide_add (x y : RawE) :
    (do let out ← NEV_AccumulateRaw.aspis_core.field.wide_exact.WideExact.add x y
        ok (toNativeE out)) =
      FIo_Native.aspis_core.field.wide_exact.WideExact.add (toNativeE x) (toNativeE y) := by
  unfold NEV_AccumulateRaw.aspis_core.field.wide_exact.WideExact.add
  cases run : FIo_Native.aspis_core.field.wide_exact.WideExact.add (toNativeE x) (toNativeE y) <;>
    simp only [run,bind_tc_ok,bind_tc_fail,bind_tc_div,native_e_reverse]
theorem wide_product (x : RawE) (q : RawQ) :
    (do let out ← NEV_AccumulateRaw.aspis_core.field.wide_exact.WideExact.mul_qm31 x q
        ok (toNativeE out)) =
      FIo_Native.aspis_core.field.wide_exact.WideExact.mul_qm31 (toNativeE x) (toNativeQ q) := by
  unfold NEV_AccumulateRaw.aspis_core.field.wide_exact.WideExact.mul_qm31
  cases run : FIo_Native.aspis_core.field.wide_exact.WideExact.mul_qm31 (toNativeE x) (toNativeQ q) <;>
    simp only [run,bind_tc_ok,bind_tc_fail,bind_tc_div,native_e_reverse]
theorem qm_product (x y : RawQ) :
    (do let out ← NEV_AccumulateRaw.aspis_core.field.QM31.mul x y
        ok (toNativeQ out)) =
      FIo_Native.aspis_core.field.QM31.mul (toNativeQ x) (toNativeQ y) := by
  unfold NEV_AccumulateRaw.aspis_core.field.QM31.mul
  cases run : FIo_Native.aspis_core.field.QM31.mul (toNativeQ x) (toNativeQ y) <;>
    simp only [run,bind_tc_ok,bind_tc_fail,bind_tc_div,native_q_reverse]
theorem from_qm (q : RawQ) :
    (do let out ← NEV_AccumulateRaw.aspis_core.field.wide_exact.WideExact.from_qm31 q
        ok (toCtorE out)) =
      NEV_CodeFieldRaw.aspis_core.field.wide_exact.WideExact.from_qm31 (toCtorQ q) := by
  unfold NEV_AccumulateRaw.aspis_core.field.wide_exact.WideExact.from_qm31
  cases run : NEV_CodeFieldRaw.aspis_core.field.wide_exact.WideExact.from_qm31 (toCtorQ q) <;>
    simp only [run,bind_tc_ok,bind_tc_fail,bind_tc_div,ctor_e_reverse]
theorem push (b : NEV_AccumulateRaw.BatchedWeights) (j : Usize) (q : RawQ) (m : U32) :
    (do let out ← NEV_AccumulateRaw.BatchedWeights.push b j q m
        ok (toPushBW out)) =
      NEI_PushRaw.BatchedWeights.push (toPushBW b) j (toPushQ q) m := by
  unfold NEV_AccumulateRaw.BatchedWeights.push
  cases run : NEI_PushRaw.BatchedWeights.push (toPushBW b) j (toPushQ q) m <;>
    simp only [toPushBW] at run ⊢ <;>
    simp only [run,bind_tc_ok,bind_tc_fail,bind_tc_div]

theorem from_m31 (ops : AspisR1.Port3_NativeQueryBody.Ops) (m : U32)
    (canonical : m.val<2147483647) :
    (do let out ← NEV_AccumulateRaw.aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.from_m31 m
        ok (NEV_AccumulateCarriers.toE out)) =
      (NBF_RowInstall.install ops).op10 m := by
  change (do let out ← (do
    let e ← NEV_CodeFieldRaw.aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.from_m31 m
    ok (fromCtorE e))
    ok (NEV_AccumulateCarriers.toE out)) = _
  simp only [bind_assoc_eq,bind_tc_ok]
  exact NEV_CodeFieldBridge.cohort ops m canonical

#print axioms native_e_reverse
#print axioms native_q_reverse
#print axioms ctor_e_reverse
#print axioms wide_add
#print axioms wide_product
#print axioms qm_product
#print axioms from_qm
#print axioms push
#print axioms from_m31
end NEV_AccumulateCallees
end
