import NEB_GeometryPrimitives
import NEA_Index
set_option autoImplicit false
noncomputable section
namespace NEB_GeometryIndices
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2
open Port3_NativeGeometryBody
open Port3_PushFrame (bind_success)

def indexPort {CoreError : Type} (error : CoreError) (u : Usize) :
    Result (core.result.Result Usize CoreError) := do
  let r ← NEA_Reference.fibre_new_ref u
  ok (match r with | .Ok f => .Ok f | .Err _ => .Err error)

def install {CoreError : Type} (ops : Ops CoreError) (error : CoreError) : Ops CoreError :=
  {NEB_GeometryPrimitives.install ops with op12:=indexPort error}

theorem accepted {CoreError : Type} (error : CoreError) (u f : Usize)
    (run : indexPort error u=ok (.Ok f)) : f=u ∧ f.val<262144 := by
  unfold indexPort at run
  obtain ⟨r,reference,run⟩ := bind_success _ _ _ run
  cases r with
  | Err e => cases run
  | Ok x =>
    cases Result.ok.inj run
    obtain ⟨same,bound⟩ := NEA_Index.accepted u f reference
    exact ⟨same,by rw [same];exact bound⟩

theorem admitted {CoreError : Type} (error : CoreError) (u : Usize)
    (bound : u.val<262144) : indexPort error u=ok (.Ok u) := by
  simp only [indexPort,NEA_Index.canonical_index u bound,bind_tc_ok]

theorem primitives {CoreError : Type} (ops : Ops CoreError) (error : CoreError) :
    Port5Q1_GeometryCanonical.SessionAPrimitives (install ops error) := by
  have p := NEB_GeometryPrimitives.primitives ops
  exact ⟨p.point,p.line,p.multiply,p.double,p.one,p.subtract⟩

/-- These are precisely the parent, left and right scalar expressions in the
emitted gather body. All index domains follow from its first accepted index. -/
theorem aligned {CoreError : Type} (error : CoreError) (u : Usize) (bound : u.val<262144) :
    ∃ parent left right : Usize,
      u / 4#usize=ok parent ∧
      left=Usize.wrapping_mul parent 4#usize ∧
      right=Usize.wrapping_add left 3#usize ∧
      left.val=u.val/4*4 ∧ right.val=u.val/4*4+3 ∧
      left.val<262144 ∧ right.val<262144 ∧
      indexPort error left=ok (.Ok left) ∧ indexPort error right=ok (.Ok right) := by
  obtain ⟨parent,division,value⟩ := UScalar.div_spec u (y:=4#usize) (by decide)
  have pv : parent.val=u.val/4 := value
  let left := Usize.wrapping_mul parent 4#usize
  let right := Usize.wrapping_add left 3#usize
  have cap : 262144 < UScalar.size .Usize := by rw [UScalar.size_def];scalar_tac
  have lv : left.val=u.val/4*4 := by
    dsimp only [left]
    rw [Usize.wrapping_mul_val_eq]
    change (parent.val*4)%UScalar.size .Usize=u.val/4*4
    rw [pv,Nat.mod_eq_of_lt (by omega)]
  have rv : right.val=u.val/4*4+3 := by
    dsimp only [right]
    rw [Usize.wrapping_add_val_eq]
    change (left.val+3)%UScalar.size .Usize=u.val/4*4+3
    rw [lv,Nat.mod_eq_of_lt (by omega)]
  have lb : left.val<262144 := by rw [lv];omega
  have rb : right.val<262144 := by rw [rv];omega
  exact ⟨parent,left,right,division,rfl,rfl,lv,rv,lb,rb,admitted error left lb,admitted error right rb⟩

#print axioms accepted
#print axioms admitted
#print axioms primitives
#print axioms aligned
end NEB_GeometryIndices
end
