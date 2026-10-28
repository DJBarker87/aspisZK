import NDO_JFu_CircleAlgebra
import NDO_JFu_Q25Source
import NDO_JFu_Q26Source
import NDO_JFm_Coordinates
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFu_CircleParameters
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation
open AspisV8R15.ExactTowerBase
open AspisV8R19.SamplerClosureProductCorrectness
open AspisR1CircleSampleWrapper

def value25 : aspis_core.field.QM31 := ⟨⟨816245010#u32,114551508#u32⟩,⟨1501205590#u32,2011200735#u32⟩⟩
def value26 : aspis_core.field.QM31 := ⟨⟨758445278#u32,139479390#u32⟩,⟨789205686#u32,1156709222#u32⟩⟩
def q25 := fromPublicQM value25
def q26 := fromPublicQM value26
def t25 : QM31Exact := decode (toR72QM q25)
def t26 : QM31Exact := decode (toR72QM q26)

theorem sample25 : _root_.sampler.qm31_sample
    (AspisV8R19.SqueezeOracleBridge.encodeState JFu_Q25Source.block)=ok q25 := by
  obtain ⟨q,call,canon,coords⟩ := SamplerTransport.sample_total
    (AspisV8R19.SqueezeOracleBridge.encodeState JFu_Q25Source.block)
  have expected : JFm_Coordinates.coordinates value25=[816245010,114551508,1501205590,2011200735] := rfl
  have same : q=value25 := JFm_Coordinates.injective (by
    rw [expected]
    simpa only [JFm_Coordinates.coordinates,JFu_Q25Source.rank,JFu_Q25Source.digits] using coords)
  rw [RawCircleSampleEmittedWrapperLaw.sampler_qm31_sample_eq_public,call,bind_tc_ok,same]
  rfl

theorem sample26 : _root_.sampler.qm31_sample
    (AspisV8R19.SqueezeOracleBridge.encodeState JFu_Q26Source.block)=ok q26 := by
  obtain ⟨q,call,canon,coords⟩ := SamplerTransport.sample_total
    (AspisV8R19.SqueezeOracleBridge.encodeState JFu_Q26Source.block)
  have expected : JFm_Coordinates.coordinates value26=[758445278,139479390,789205686,1156709222] := rfl
  have same : q=value26 := JFm_Coordinates.injective (by
    rw [expected]
    simpa only [JFm_Coordinates.coordinates,JFu_Q26Source.rank,JFu_Q26Source.digits] using coords)
  rw [RawCircleSampleEmittedWrapperLaw.sampler_qm31_sample_eq_public,call,bind_tc_ok,same]
  rfl

theorem canon25 : Canonical (toR72QM q25) := by
  change 816245010<2147483647 ∧ 114551508<2147483647 ∧
    1501205590<2147483647 ∧ 2011200735<2147483647
  omega

theorem canon26 : Canonical (toR72QM q26) := by
  change 758445278<2147483647 ∧ 139479390<2147483647 ∧
    789205686<2147483647 ∧ 1156709222<2147483647
  omega

theorem outside25 : t25.im ≠ 0 := by
  intro h
  have c := congrArg (fun x : CM31Exact => x.re) h
  change (1501205590 : M31Exact)=0 at c
  have hv := congrArg (fun x : M31Exact => ZMod.val x) c
  change 1501205590=0 at hv
  omega

theorem outside26 : t26.im ≠ 0 := by
  intro h
  have c := congrArg (fun x : CM31Exact => x.re) h
  change (789205686 : M31Exact)=0 at c
  have hv := congrArg (fun x : M31Exact => ZMod.val x) c
  change 789205686=0 at hv
  omega

theorem different : t25 ≠ t26 := by
  intro h
  have c := congrArg (fun x : QM31Exact => x.im.re) h
  change (1501205590 : M31Exact)=(789205686 : M31Exact) at c
  have hv := congrArg (fun x : M31Exact => ZMod.val x) c
  change 1501205590=789205686 at hv
  omega

#print axioms sample25
#print axioms sample26
#print axioms canon25
#print axioms canon26
#print axioms outside25
#print axioms outside26
#print axioms different
end AspisR1.JFu_CircleParameters
end
