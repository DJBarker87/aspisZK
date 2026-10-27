import LPp_FallbackValues

set_option autoImplicit false
noncomputable section
namespace LPp.MapperValues
open Aeneas Aeneas.Std Result AspisR1CircleFallback
open AspisV8R19.SamplerClosureCircleSourceExecution
open AspisV8R19.SamplerCirclePolicy
open R0P.SemSource
open RawCircleFallbackOutputBridge

def parameter0 : field.QM31 := ⟨field.CM31.ZERO, field.CM31.ONE⟩
def parameter1 : field.QM31 := ⟨field.CM31.ONE, field.CM31.ONE⟩

def native0 : circle.SecureCirclePoint :=
  ⟨⟨⟨429496729#u32,1288490188#u32⟩,⟨0#u32,0#u32⟩⟩,
   ⟨⟨0#u32,0#u32⟩,⟨429496730#u32,1288490188#u32⟩⟩⟩
def native1 : circle.SecureCirclePoint :=
  ⟨⟨⟨1420643028#u32,1949254387#u32⟩,⟨1123299138#u32,892031669#u32⟩⟩,
   ⟨⟨627725989#u32,561649569#u32⟩,⟨396458520#u32,693802409#u32⟩⟩⟩

theorem native0_port : fromR72Point (encodePoint (LPp.Fallback.x0,LPp.Fallback.y0)) = native0 := by rfl
theorem native1_port : fromR72Point (encodePoint (LPp.Fallback.x1,LPp.Fallback.y1)) = native1 := by rfl

theorem mapper0 : circle.secure_ood_circle_point_from_parameter parameter0 = .ok (.Ok native0) := by
  have h := generated_parameter0_output
  rw [LPp.Fallback.point0, native0_port] at h
  exact h

theorem mapper1 : circle.secure_ood_circle_point_from_parameter parameter1 = .ok (.Ok native1) := by
  have h := generated_parameter1_output
  rw [LPp.Fallback.point1, native1_port] at h
  exact h

theorem defensive0_unreachable (e : circle.CirclePointError) :
    circle.secure_ood_circle_point_from_parameter parameter0 ≠ .ok (.Err e) := by
  rw [mapper0]; simp

theorem defensive1_unreachable (e : circle.CirclePointError) :
    circle.secure_ood_circle_point_from_parameter parameter1 ≠ .ok (.Err e) := by
  rw [mapper1]; simp

#print axioms native0_port
#print axioms native1_port
#print axioms mapper0
#print axioms mapper1
#print axioms defensive0_unreachable
#print axioms defensive1_unreachable
end LPp.MapperValues
