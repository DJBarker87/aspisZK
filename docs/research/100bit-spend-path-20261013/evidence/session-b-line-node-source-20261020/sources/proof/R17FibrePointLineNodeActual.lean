import R17FibrePointActualSuccess
import R17FibrePointLineNode

open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false

namespace R17FibrePointLineNodeActual
open AspisR1QueryGeometryActual AspisCircleGroupOrder

/-- Explicit semantic boundary for the three scalar M31 operations retained
opaque by the focused Aeneas source cut. -/
structure M31Ops where
  mul : field.M31 → field.M31 → Result field.M31
  double : field.M31 → Result field.M31
  sub : field.M31 → field.M31 → Result field.M31

def decoded (x : field.M31) : ZMod AspisCircleGroupOrder.P :=
  R17FibrePointDecodedProduct.decodeM31 x

structure M31OpsSemantics (ops : M31Ops) : Prop where
  mul_spec : ∀ a b z, ops.mul a b = .ok z → decoded z = decoded a * decoded b
  double_spec : ∀ a z, ops.double a = .ok z → decoded z = decoded a + decoded a
  sub_spec : ∀ a b z, ops.sub a b = .ok z → decoded z = decoded a - decoded b

theorem decoded_source_one : decoded (1#u32) = 1 := by rfl

/-- Source-shaped parameterization of the exact extracted line_node body.
The actual generated owner calls opaque scalar operations; `ops` exposes those
operations so their arithmetic law can remain an explicit boundary. -/
def line_node (cmops : CM31Ops) (ops : M31Ops) (u : domain.FibreIndex) :
    Result field.M31 := do
  let p ← fast_domain.fibre_point cmops u
  let square ← ops.mul p.x p.x
  let m ← ops.double square
  ops.sub m (1#u32)

private theorem bind_ok_inv {α β : Type} {r : Result α} {f : α → Result β}
    {x : β} (h : Bind.bind r f = .ok x) :
    ∃ a, r = .ok a ∧ f a = .ok x := by
  cases r with
  | ok a => exact ⟨a, rfl, h⟩
  | fail e => simp [Bind.bind] at h
  | div => simp [Bind.bind] at h

/-- A successful execution of the exact line_node sequencing produces the
stored FirstLineX18 value, provided the extracted fibre-point CM31 laws and
the scalar M31 operation laws hold. -/
theorem successful_line_node_stored
    (cmops : CM31Ops)
    (hcm : R17FibrePointDecodedProduct.CM31OpsSemantics cmops)
    (ops : M31Ops) (hm : M31OpsSemantics ops)
    (u : domain.FibreIndex) (hu : u.val < 262144)
    (out : field.M31) (hline : line_node cmops ops u = .ok out) :
    decoded out = AspisV7ExactOneFoldDomains.storedFirstLineX18
      (⟨u.val, hu⟩ : Fin 262144) := by
  have h := hline
  unfold line_node at h
  rcases bind_ok_inv h with ⟨p, hp, hrest1⟩
  rcases bind_ok_inv hrest1 with ⟨square, hsquare, hrest2⟩
  rcases bind_ok_inv hrest2 with ⟨m, hmrun, hsub⟩
  have hvalue := R17FibrePointLineNode.successful_call_stored_line_x
    cmops hcm u hu p hp
  have hformula : decoded out =
      2 * decoded p.x ^ 2 - 1 := by
    rw [hm.sub_spec m (1#u32) out hsub, decoded_source_one,
      hm.double_spec square m hmrun,
      hm.mul_spec p.x p.x square hsquare]
    ring
  calc
    decoded out = 2 * decoded p.x ^ 2 - 1 := hformula
    _ = 2 * (R17FibrePointDecodedProduct.decodePoint p).1 ^ 2 - 1 := by rfl
    _ = AspisV7ExactOneFoldDomains.storedFirstLineX18
        (⟨u.val, hu⟩ : Fin 262144) := hvalue

#print axioms successful_line_node_stored
end R17FibrePointLineNodeActual
