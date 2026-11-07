import LIB_VCarriers
import LIB_Env
set_option autoImplicit false
noncomputable section
namespace LIBC_PreparedCarriers
open Aeneas Aeneas.Std RSL
/-- Representation equalities only. The concrete VLib bundle discharges every
field by rfl; this record carries no operation or child-result assumption. -/
structure Types (V : VLib) : Prop where
 challenges : V.Challenges = LIB_VCarriers.Challenges
 alpha : V.Alpha = LIB_VCarriers.Alpha
 claims : V.Claims = LIB_VCarriers.Claims
 k29 : V.K29 = LIB_VCarriers.K29
 point : V.Point = LIB_VCarriers.Point
 transcript : V.Transcript = LIB_VCarriers.Transcript
 view : V.View = LIB_VCarriers.View
 prepared : V.Prepared = LIB_VCarriers.Prepared
 e29 : V.E29 = LIB_VCarriers.E29
 error : V.VErr = LIB_VCarriers.VErr
/-- All fields of the SAME semantic result, with no independently chosen
Verified value. Fixed-array construction preserves the two original slots. -/
def verified {V : VLib} (t : Types V) (s : Verified V) :
 AspisR1PublicPreparation.r1_semantic.Verified Unit :=
 {roots := Array.make 2#usize [LIB_Env.nativeKey s.roots.1,LIB_Env.nativeKey s.roots.2]
  challenges := LIB_VCarriers.challengesRaw (t.challenges ▸ s.challenges)
  alpha := LIB_VCarriers.alphaRaw (t.alpha ▸ s.alpha)
  claims := LIB_VCarriers.claimsRaw (t.claims ▸ s.claims)
  extra := LIB_VCarriers.k29Raw (t.k29 ▸ s.extra)
  before_z1 := LIB_VCarriers.k29Raw (t.k29 ▸ s.before_z1)
  state_before_z0 := LIB_Env.nativeKey s.state_before_z0
  z := Array.make 2#usize [Eq.mp t.point s.z.1,Eq.mp t.point s.z.2]
  transcript := Eq.mp t.transcript s.transcript}
def input {V : VLib} (t : Types V) (a : Verified V × V.View × V.E29) :
 AspisR1PublicPreparation.r1_semantic.Verified Unit × LIB_VCarriers.View × LIB_VCarriers.E29 :=
 (verified t a.1,t.view ▸ a.2.1,t.e29 ▸ a.2.2)
def output {V : VLib} (t : Types V)
 (r : Except LIB_VCarriers.VErr LIB_VCarriers.Prepared × LIB_VCarriers.E29) :
 Except V.VErr V.Prepared × V.E29 :=
 ((match r.1 with
   | .ok p => .ok (t.prepared.symm ▸ p)
   | .error e => .error (t.error.symm ▸ e)),t.e29.symm ▸ r.2)
theorem input_scratch {V : VLib} (t : Types V) (a : Verified V × V.View × V.E29) :
 (input t a).2.2 = (t.e29 ▸ a.2.2) := rfl
theorem output_error {V : VLib} (t : Types V) (e : LIB_VCarriers.VErr) (g : LIB_VCarriers.E29) :
 output t (.error e,g) = (.error (t.error.symm ▸ e),t.e29.symm ▸ g) := rfl
theorem output_success {V : VLib} (t : Types V) (p : LIB_VCarriers.Prepared) (g : LIB_VCarriers.E29) :
 output t (.ok p,g) = (.ok (t.prepared.symm ▸ p),t.e29.symm ▸ g) := rfl
theorem state_before {V : VLib} (t : Types V) (s : Verified V) :
 LIB_Carriers.b32 (verified t s).state_before_z0 = s.state_before_z0 := LIB_Env.key_roundtrip _
#print axioms input_scratch
#print axioms output_error
#print axioms output_success
#print axioms state_before
end LIBC_PreparedCarriers
