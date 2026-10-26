import R1Z.ProverRw18FieldMeaning
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw18FieldInjective
open Aeneas Aeneas.Std ProverRw18FieldMeaning

theorem word (x y : U32) (hx : x.val<AspisCircleGroupOrder.P)
    (hy : y.val<AspisCircleGroupOrder.P)
    (same : (x.val : AspisV8R15.ExactTowerBase.M31Exact)=(y.val : AspisV8R15.ExactTowerBase.M31Exact)) :
    x=y := by
  apply UScalar.eq_of_val_eq
  have values := congrArg ZMod.val same
  rw [ZMod.val_natCast_of_lt hx,ZMod.val_natCast_of_lt hy] at values
  exact values

theorem raw (x y : Raw) (hx : Canonical x) (hy : Canonical y) (same : decode x=decode y) :
    x=y := by
  rcases x with ⟨⟨xa,xb⟩,⟨xc,xd⟩⟩
  rcases y with ⟨⟨ya,yb⟩,⟨yc,yd⟩⟩
  have a : xa=ya := word xa ya hx.1.1 hy.1.1 (congrArg (fun q : K => q.re.re) same)
  have b : xb=yb := word xb yb hx.1.2 hy.1.2 (congrArg (fun q : K => q.re.im) same)
  have c : xc=yc := word xc yc hx.2.1 hy.2.1 (congrArg (fun q : K => q.im.re) same)
  have d : xd=yd := word xd yd hx.2.2 hy.2.2 (congrArg (fun q : K => q.im.im) same)
  cases a; cases b; cases c; cases d
  rfl

theorem full (x y : Raw) (hx : Canonical x) (hy : Canonical y) (same : decode x=decode y) :
    ProverRw18FieldMeaning.full x=ProverRw18FieldMeaning.full y :=
  congrArg ProverRw18FieldMeaning.full (raw x y hx hy same)

#print axioms word
#print axioms raw
#print axioms full
end R1Z.ProverRw18FieldInjective
