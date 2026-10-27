import FIo_Install
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIp_Equality
open Aeneas Aeneas.Std Result
abbrev NC := FIo_Native.aspis_core.field.CM31
abbrev NQ := FIo_Native.aspis_core.field.QM31
abbrev E := AspisR1Stage2.Stage2Finish.E

theorem cm (x y : NC) : FIo_Native.aspis_core.field.CM31.Insts.CoreCmpPartialEqCM31.eq x y=ok (decide (x=y)) := by
  cases x with | mk a b =>
    cases y with | mk a' b' =>
      by_cases ha : a=a' <;> by_cases hb : b=b' <;>
        simp_all [FIo_Native.aspis_core.field.CM31.Insts.CoreCmpPartialEqCM31.eq,
          FIo_Native.aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq,bind_tc_ok]

theorem qm (x y : NQ) : FIo_Native.aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.eq x y=ok (decide (x=y)) := by
  cases x with | mk a b =>
    cases y with | mk a' b' =>
      by_cases ha : a=a' <;> by_cases hb : b=b' <;>
        simp_all [FIo_Native.aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.eq,cm,bind_tc_ok]

/-- Derived field PartialEq compares the same two QM31 coordinates in order. -/
def eq (x y : E) : Result Bool := do
  let same ← FIo_Native.aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.eq
    (FIo_Install.toE x).c0 (FIo_Install.toE y).c0
  if same then FIo_Native.aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.eq
    (FIo_Install.toE x).c1 (FIo_Install.toE y).c1 else ok false

def dictionary : core.cmp.PartialEq E E := {eq:=eq}

#print axioms cm
#print axioms qm
end AspisR1.FIp_Equality
end
