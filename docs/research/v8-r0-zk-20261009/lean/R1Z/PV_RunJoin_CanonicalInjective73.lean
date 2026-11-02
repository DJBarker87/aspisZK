import R1Z.PV_RunJoin_BoundaryPolynomial73
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CanonicalInjective73
open Aeneas Aeneas.Std ProverRwFull
open PV_RunJoin_FieldData34 (value canonical)

theorem word (x y : U32) (hx : x.val<AspisCircleGroupOrder.P) (hy : y.val<AspisCircleGroupOrder.P)
    (eq : (x.val : ZMod AspisCircleGroupOrder.P)=(y.val : ZMod AspisCircleGroupOrder.P)) : x=y := by
  apply UScalar.eq_of_val_eq
  have h := congrArg ZMod.val eq
  simpa only [ZMod.val_natCast,Nat.mod_eq_of_lt hx,Nat.mod_eq_of_lt hy] using h

theorem complete (x y : aspis_core.field.QM31) (hx : canonical x) (hy : canonical y)
    (eq : value x=value y) : x=y := by
  have limbs (k : Fin 4) :
      ((PV_RunJoin_BoundaryPolynomial73.limb x k).val : ZMod AspisCircleGroupOrder.P)=
      ((PV_RunJoin_BoundaryPolynomial73.limb y k).val : ZMod AspisCircleGroupOrder.P) := by
    simpa only [PV_RunJoin_BoundaryPolynomial73.component_decode] using
      congrArg (fun q => PV_RunJoin_BoundaryPolynomial73.component q k) eq
  have a := word x.c0.a y.c0.a hx.1.1 hy.1.1 (limbs 0)
  have b := word x.c0.b y.c0.b hx.1.2 hy.1.2 (limbs 1)
  have c := word x.c1.a y.c1.a hx.2.1 hy.2.1 (limbs 2)
  have d := word x.c1.b y.c1.b hx.2.2 hy.2.2 (limbs 3)
  cases x with
  | mk x0 x1 =>
    cases y with
    | mk y0 y1 =>
      cases x0;cases x1;cases y0;cases y1
      congr 2 <;> assumption

#print axioms word
#print axioms complete
end R1Z.PV_RunJoin_CanonicalInjective73
