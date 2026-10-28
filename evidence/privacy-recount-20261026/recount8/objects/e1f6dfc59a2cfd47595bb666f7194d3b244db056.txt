import R1Z.PV_RunJoin_WeightMap46
import R1Z.ProverRwP6ArrayMap
set_option autoImplicit false
namespace R1Z.PV_RunJoin_WeightBorrow46
open Aeneas Aeneas.Std Result
open PV_B2_F_ConstructorCarrier (amap)

theorem complete {A B : Type} {n : Usize} (a : Array A n) (i : Usize)
    (k : A → (A → Array A n) → Result B) :
    (do let (x,back) ← Array.index_mut_usize a i; k x back)=
      (do let x ← Array.index_usize a i; k x (Aeneas.Std.Array.set a i)) := by
  unfold Array.index_mut_usize
  simp only [bind_assoc,bind_tc_ok]

theorem restore {A B : Type} {n : Usize} (f : A → B) (a : Array A n)
    (i : Usize) (x : A) :
    amap f (Aeneas.Std.Array.set a i x)=Aeneas.Std.Array.set (amap f a) i (f x) :=
  ProverRwP6ArrayMap.set_map f a i x

#print axioms complete
#print axioms restore
end R1Z.PV_RunJoin_WeightBorrow46
