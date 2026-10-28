import R1Z.ProverRwFullExternalFuns
import R1Z.PV_FXM_ZeroWorld
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_FXM_ZeroSelected
open Aeneas Aeneas.Std ProverRwFull
variable [ExternalTypes]

/-- Value projection of the blanket operation. Volatile and fence effects
are interpreted separately by ZeroWorld, and never identified with a no-op. -/
def scalar {Z : Type} (d : zeroize.DefaultIsZeroes Z) (_ : Z) : Result Z :=
  d.coredefaultDefaultInst.default

/-- Every updated element is retained; no discarded borrow continuation. -/
def elements {Z : Type} (d : zeroize.Zeroize Z) :
    (xs : List Z) → Result {ys : List Z // ys.length=xs.length}
  | [] => .ok ⟨[],rfl⟩
  | x::xs => do
    let y ← d.zeroize x
    let ys ← elements d xs
    .ok ⟨y::ys.val,congrArg Nat.succ ys.property⟩

def array {Z : Type} {N : Usize} (d : zeroize.Zeroize Z) (a : Array Z N) :
    Result (Array Z N) := do
  let ys ← elements d a.val
  .ok ⟨ys.val,ys.property.trans a.property⟩

@[reducible] def selected (ops : ExternalFuns) : ExternalFuns :=
  {ops with op122 := array, op123 := scalar}

/-- The actual byte dictionary, rather than an arbitrary Default callback. -/
def byteDefault : zeroize.DefaultIsZeroes U8 :=
  ⟨core.marker.CopyU8,core.default.DefaultU8⟩
def byteZero : zeroize.Zeroize U8 := ⟨scalar byteDefault⟩

theorem byte_value (x : U8) : scalar byteDefault x = .ok 0#u8 := rfl

theorem byte_step (x : U8) : byteZero.zeroize x = .ok 0#u8 := rfl

theorem elements_value (xs : List U8) :
    elements byteZero xs = .ok ⟨List.replicate xs.length 0#u8,by simp⟩ := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [elements,byte_step,ih,bind_tc_ok,List.length_cons,
      List.replicate_succ]

theorem array_value {N : Usize} (a : Array U8 N) :
    array byteZero a = .ok (Array.repeat N 0#u8) := by
  simp only [array,elements_value,bind_tc_ok]
  congr 1
  apply Subtype.ext
  exact congrArg (fun n => List.replicate n 0#u8) a.property

theorem scalar_installed (ops : ExternalFuns) (x : U8) :
    (selected ops).op123 byteDefault x = .ok 0#u8 := byte_value x

theorem array_installed (ops : ExternalFuns) {N : Usize} (a : Array U8 N) :
    (selected ops).op122 byteZero a = .ok (Array.repeat N 0#u8) := array_value a

theorem other_fields (ops : ExternalFuns) :
    {selected ops with op122 := ops.op122,op123 := ops.op123}=ops := rfl

/-- The caller receives the zero value and the post-write world, including
all byte writes and fences. This is not a value-only erasure claim. -/
theorem execution {F A : Type} (ops : ExternalFuns) {N : Usize}
    (a : Array U8 N) (address : Nat) (w : PV_FXM_ZeroWorld.World F)
    (caller : Array U8 N → PV_FXM_ZeroWorld.World F → Result A) :
    (do let a' ← (selected ops).op122 byteZero a
        caller a' (PV_FXM_ZeroWorld.native address N.val w)) =
      caller (Array.repeat N 0#u8) (PV_FXM_ZeroWorld.indexed address 0 N.val w) := by
  rw [array_installed]
  simp only [bind_tc_ok]
  exact PV_FXM_ZeroWorld.caller_composition address N.val w (caller (Array.repeat N 0#u8))

theorem scalar_execution {F A : Type} (ops : ExternalFuns) (x : U8)
    (address : Nat) (w : PV_FXM_ZeroWorld.World F)
    (caller : U8 → PV_FXM_ZeroWorld.World F → Result A) :
    (do let x' ← (selected ops).op123 byteDefault x
        caller x' (PV_FXM_ZeroWorld.byte address w)) =
      caller 0#u8 (PV_FXM_ZeroWorld.byte address w) := by
  rw [scalar_installed]
  rfl

#print axioms byte_step
#print axioms scalar_execution
#print axioms byte_value
#print axioms elements_value
#print axioms array_value
#print axioms scalar_installed
#print axioms array_installed
#print axioms other_fields
#print axioms execution
end R1Z.PV_FXM_ZeroSelected
