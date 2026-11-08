import PV_LIB_A_PrefixNativeCalls14
import PV_LIB_A_PrefixStructuredCalls14
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_V2PrefixTables14
open PV_STX2_Syntax PV_LIB_A_StructuredFrontier13

/-- Exact emitted lookup fragment of a machine specification. No function law,
reply, Store transformer, future success or OWNER frame is a field. Every entry
names the actual source descriptor, allowing the ORIGINAL caller's fixed table. -/
structure Tables (P : Data → Option PV_STX2_SliceSyntax.Program) : Prop where
  native121 : P (fn PV_LIB_A_PrefixNativeCalls14.src121) = none
  native122 : P (fn PV_LIB_A_PrefixNativeCalls14.src122) = none
  native123 : P (fn PV_LIB_A_PrefixNativeCalls14.src123) = none
  native124 : P (fn PV_LIB_A_PrefixNativeCalls14.src124) = none
  native134 : P (fn PV_LIB_A_PrefixNativeCalls14.src134) = none
  native410 : P (fn PV_LIB_A_PrefixNativeCalls14.src410) = none
  body125 : P (fn PV_LIB_A_PrefixStructuredCalls14.src125) = some PV_THR2_F125.live
  body219 : P (fn PV_LIB_A_PrefixStructuredCalls14.src219) = some PV_THR2_F219.live
  body220 : P (fn PV_LIB_A_PrefixStructuredCalls14.src220) = some PV_THR2_F220.live
  body208 : P (fn PV_LIB_A_PrefixStructuredCalls14.src208) = some PV_THR2_F208.live
  body15 : P (fn PV_LIB_A_PrefixStructuredCalls14.src15) = some PV_THR2_F15.live

/-- The existing fully installed prefix table discharges this fragment BY NAME.
This does not bind lane C's runtime or replace its retained Full.programs. -/
theorem installed (P : Data → Option PV_STX2_SliceSyntax.Program) :
    Tables (PV_LIB_A_SpawnEnter12.enter270Programs P) :=
  ⟨PV_LIB_A_PrefixNativeCalls14.child121 P,PV_LIB_A_PrefixNativeCalls14.child122 P,
   PV_LIB_A_PrefixNativeCalls14.child123 P,PV_LIB_A_PrefixNativeCalls14.child124 P,
   PV_LIB_A_PrefixNativeCalls14.child134 P,PV_LIB_A_PrefixNativeCalls14.child410 P,
   PV_LIB_A_PrefixStructuredCalls14.lookup125 P,PV_LIB_A_PrefixStructuredCalls14.lookup219 P,
   PV_LIB_A_PrefixStructuredCalls14.lookup220 P,PV_LIB_A_PrefixStructuredCalls14.lookup208 P,
   PV_LIB_A_PrefixStructuredCalls14.lookup15 P⟩

#print axioms Tables
#print axioms installed
end PV_LIB_A_V2PrefixTables14
