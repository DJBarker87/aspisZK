import LIB_VArray
set_option autoImplicit false
noncomputable section
namespace LIB_VChallenges
open Aeneas Aeneas.Std LIB_VCarriers
open LIB_VScalarCarriers (CanonicalRaw ofRaw toRaw)
open AspisR1PublicPreparation
abbrev Raw := r1_wire.Challenges
def Canonical (c : Raw) : Prop :=
 CanonicalRaw c.lambda ∧ CanonicalRaw c.chi ∧ CanonicalRaw c.theta ∧
 CanonicalRaw c.mu ∧ CanonicalRaw c.eta ∧ LIB_VArray.Canonical c.zc
def lift (c : Raw) (h : Canonical c) : Challenges :=
 ⟨ofRaw c.lambda h.1,ofRaw c.chi h.2.1,ofRaw c.theta h.2.2.1,
  LIB_VArray.lift c.zc h.2.2.2.2.2,ofRaw c.mu h.2.2.2.1,ofRaw c.eta h.2.2.2.2.1⟩
theorem raw_lift (c : Raw) (h : Canonical c) : challengesRaw (lift c h) = c := by
 cases c
 simp only [challengesRaw,lift,LIB_VScalarCarriers.toRaw_ofRaw]
 congr 1
 exact LIB_VArray.raw_lift _ _
theorem begin_canonical (D : aspis_core.Digest32 Unit) (p : Prefix) (t after : Transcript)
 (c : Raw) (run : r1_wire.begin D (prefixRaw p) t = .ok (.Ok c,after)) : Canonical c :=
 AspisR1.FJn_BeginCanonical.value D (prefixRaw p) t after c run
#print axioms raw_lift
#print axioms begin_canonical
end LIB_VChallenges
