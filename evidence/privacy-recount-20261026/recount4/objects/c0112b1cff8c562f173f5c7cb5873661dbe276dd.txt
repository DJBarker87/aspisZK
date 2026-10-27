import AspisR1ProducerRelease47.Kernels49
import R1Z.ProverCommitNativeC49
/-! Symbolic correctness of the optimized complex square, including every
wrapping U64 intermediate. No concrete field exponent is normalized. -/
set_option autoImplicit false
namespace R1Z.ProverCommitNativeSquare49
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47 ProverCommitNativeC49
open AspisV8R15.ExactTowerBase
abbrev P : Nat := AspisCircleGroupOrder.P

def operand (a b : U32) : U64 :=
  U64.wrapping_mul
    (U64.wrapping_add (core.convert.num.FromU64U32.from a) (core.convert.num.FromU64U32.from b))
    (U64.wrapping_sub (U64.wrapping_add (core.convert.num.FromU64U32.from a)
      (core.convert.num.FromU64U32.from field.P)) (core.convert.num.FromU64U32.from b))

theorem widen (a : U32) : (core.convert.num.FromU64U32.from a).val=a.val := by scalar_tac

theorem add64 (x y : U64) (h : x.val+y.val<2^64) :
    (U64.wrapping_add x y).val=x.val+y.val := by
  rw [U64.wrapping_add_val_eq,UScalar.size_def]
  exact Nat.mod_eq_of_lt h

theorem sub64 (x y : U64) (h : y.val≤x.val) :
    (U64.wrapping_sub x y).val=x.val-y.val := by
  rw [U64.wrapping_sub_val_eq,UScalar.size_def]
  change (x.val+(2^64-y.val))%2^64=x.val-y.val
  have hx : x.val<2^64 := x.bv.isLt
  have hy : y.val<2^64 := y.bv.isLt
  rw [show x.val+(2^64-y.val)=(x.val-y.val)+2^64 by omega,Nat.add_mod]
  simp only [Nat.mod_self,Nat.add_zero,Nat.mod_mod]
  exact Nat.mod_eq_of_lt (by omega)

theorem mul64 (x y : U64) (h : x.val*y.val<2^64) :
    (U64.wrapping_mul x y).val=x.val*y.val := by
  rw [U64.wrapping_mul_val_eq,UScalar.size_def]
  exact Nat.mod_eq_of_lt h

theorem operand_value (a b : U32) (ha : a.val<P) (hb : b.val<P) :
    (operand a b).val=(a.val+b.val)*(a.val+P-b.val) := by
  have hp : field.P.val=P := by rw [field.P];rfl
  have hl : a.val+b.val<2^32 := by change a.val<2147483647 at ha;change b.val<2147483647 at hb;omega
  have hr : a.val+P-b.val<2^32 := by change a.val<2147483647 at ha;change b.val<2147483647 at hb;change a.val+2147483647-b.val<2^32;omega
  have hbase : a.val+P<2^64 := by change a.val<2147483647 at ha;change a.val+2147483647<2^64;omega
  let l := U64.wrapping_add (core.convert.num.FromU64U32.from a) (core.convert.num.FromU64U32.from b)
  let c := U64.wrapping_add (core.convert.num.FromU64U32.from a) (core.convert.num.FromU64U32.from field.P)
  let r := U64.wrapping_sub c (core.convert.num.FromU64U32.from b)
  have lv : l.val=a.val+b.val := add64 _ _ (by rw [widen,widen];omega)
  have cv : c.val=a.val+P := by apply (add64 _ _ (by rw [widen,widen,hp];exact hbase)).trans;rw [widen,widen,hp]
  have rv : r.val=a.val+P-b.val := by
    dsimp only [r]
    rw [sub64 _ _ (by rw [cv,widen];omega),cv,widen]
  have hmul : l.val*r.val<2^64 := by
    rw [lv,rv]
    calc
      _ < 2^32*2^32 := Nat.mul_lt_mul_of_lt_of_lt hl hr
      _ = _ := by decide
  exact (mul64 l r hmul).trans (by rw [lv,rv])

theorem reduce_exact (x : U64) :
    ∃ z : U32, field.M31.reduce_u64 x=ok z ∧ z.val<P ∧
      (z.val : M31Exact)=(x.val : M31Exact) := by
  obtain ⟨z,hz,hv,hc⟩ := AspisR1.ExtractedCurrentReducer.current_reduce_mod x
  have checked : AspisR1ProducerChecked47.field.reduce_u64 x=ok z := by
    rw [ProverCommitPrimitive47.reduce,hz]
  have h := ProverCommitRelease47.reduce x z checked
  refine ⟨z,?_,hc,?_⟩
  · simp only [field.M31.reduce_u64,h,bind_tc_ok,id_eq]
  · rw [hv,ZMod.natCast_mod]

theorem square (x : Old.C) (hx : Canonical x) :
    ∃ z : Old.C, field.CM31.square (source x)=ok (source z) ∧
      Canonical z ∧ value z=value x*value x := by
  obtain ⟨a,ha,hca,hva⟩ := reduce_exact (operand x.a x.b)
  obtain ⟨ab,hab,hcab,hvab⟩ := ProverCommitM31Ops48.mul_exact x.a x.b
  obtain ⟨b,hb,hcb,hvb⟩ := ProverCommitM31Ops48.add_exact ab ab hcab hcab
  dsimp only [operand] at ha
  refine ⟨⟨a,b⟩,?_,⟨hca,hcb⟩,?_⟩
  · simp only [field.CM31.square,field.M31.double,source,ProverCommitRelease47.convC,fromC,
      ha,hab,hb,lift,bind_tc_ok]
  · rw [operand_value x.a x.b hx.1 hx.2] at hva
    have hr : (a.val : M31Exact)=(x.a.val : M31Exact)^2-(x.b.val : M31Exact)^2 := by
      rw [hva,Nat.cast_mul,Nat.cast_add,Nat.cast_sub (by have hh : x.b.val<P := hx.2;omega),Nat.cast_add]
      simp only [show (P : M31Exact)=0 from ZMod.natCast_self P,add_zero]
      ring
    apply QuadraticAlgebra.ext
    · change (a.val : M31Exact)=(x.a.val : M31Exact)*(x.a.val : M31Exact)+(-1)*(x.b.val : M31Exact)*(x.b.val : M31Exact)
      rw [hr];ring
    · change ProverCommitM31Ops48.decode b=_
      rw [hvb,hvab]
      change (x.a.val : M31Exact)*(x.b.val : M31Exact)+(x.a.val : M31Exact)*(x.b.val : M31Exact)=_
      simp only [QuadraticAlgebra.im_mul]
      change (x.a.val : M31Exact)*(x.b.val : M31Exact)+(x.a.val : M31Exact)*(x.b.val : M31Exact)=(x.a.val : M31Exact)*(x.b.val : M31Exact)+(x.b.val : M31Exact)*(x.a.val : M31Exact)+0*(x.b.val : M31Exact)*(x.b.val : M31Exact)
      ring

#print axioms widen
#print axioms add64
#print axioms sub64
#print axioms mul64
#print axioms operand_value
#print axioms reduce_exact
#print axioms square
end R1Z.ProverCommitNativeSquare49
