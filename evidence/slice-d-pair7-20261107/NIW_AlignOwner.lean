import NIT_NewPortInstantiation
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIW_AlignOwner
open Aeneas Aeneas.Std Result NIT_Cuts AspisR1Stage2

theorem mapArray_injective {A B : Type} {n : Usize} (f : A → B) (hf : Function.Injective f) :
 Function.Injective (FIn_WeightsInstall.mapArray (n:=n) f) := by
 have lists : ∀ xs ys : List A, xs.map f=ys.map f → xs=ys := by
  intro xs
  induction xs with
  | nil => intro ys h;cases ys with
    | nil=>rfl
    | cons y ys=>cases h
  | cons x xs ih =>
    intro ys h
    cases ys with
    | nil=>cases h
    | cons y ys=>
     have pair := List.cons.inj h
     exact congrArg₂ List.cons (hf pair.1) (ih ys pair.2)
 intro a b same
 apply Subtype.ext
 exact lists a.val b.val (congrArg Subtype.val same)

theorem toQ_injective : Function.Injective FIo_Install.toQ := by
 intro a b h
 cases a with
 | mk a0 a1=>
  cases a0;cases a1
  cases b with
  | mk b0 b1=>cases b0;cases b1;cases h;rfl

theorem variant_injective : Function.Injective FIo_Install.variant := by
 intro a b h
 cases a <;> cases b <;> cases h <;> rfl

/-- Equality of all observed raw fields identifies the decoded owned payload;
no normalization, canonical-input restriction, or pointer equality is used. -/
theorem toWeights_injective : Function.Injective FIo_Install.toWeights := by
 intro a b h
 have hv := variant_injective (congrArg FIo_Native.weights.Weights.variant h)
 have hq := mapArray_injective (n:=4#usize) FIo_Install.toQ toQ_injective
 have hrow := mapArray_injective (n:=5#usize) (FIn_WeightsInstall.mapArray FIo_Install.toQ) hq
 have hf := mapArray_injective (n:=5#usize)
  (FIn_WeightsInstall.mapArray (FIn_WeightsInstall.mapArray FIo_Install.toQ)) hrow
  (congrArg FIo_Native.weights.Weights.factors h)
 have hp := mapArray_injective (n:=3#usize) (FIn_WeightsInstall.mapArray FIo_Install.toQ)
  (mapArray_injective (n:=10#usize) FIo_Install.toQ toQ_injective)
  (congrArg FIo_Native.weights.Weights.points h)
 have he := mapArray_injective (n:=2#usize) FIo_Install.toQ toQ_injective
  (congrArg FIo_Native.weights.Weights.extra h)
 cases a;cases b;cases hv;cases hf;cases hp;cases he;rfl

/-- Supplemental NEW ownership observation, separate from cutNewPort's argument
observations. Whole Weights construction K005 timed out; K006+ factors and
rest windows use the SAME by-value Option<Box<Weights>> move. -/
def cutPayload (before after : NewPort) (out : Reply (Ref FIo_Install.W)) : Prop :=
 before.calls=0 ∧ after.calls=1 ∧
 match out with
 | .Ok value=>∃ child,before.reply=some child ∧
   (FIo_Install.toWeights child.value).variant=FIo_Native.transport.Variant.S2 ∧
   before.error=none ∧ after.reply=none ∧ value.address=child.address ∧
   FIo_Install.toWeights value.value=FIo_Install.toWeights child.value
 | .Err e=>before.error=some e

/-- Actual native returned Box payload is the actual pre-call child payload,
by the observed raw-field windows. The old address-only cut is insufficient. -/
theorem returned (before after : NewPort) (out : Ref FIo_Install.W)
 (native : cutPayload before after (.Ok out)) :
 ∃ child,before.reply=some child ∧ out=child := by
 obtain ⟨_,_,child,reply,_,_,_,address,payload⟩ := native
 have same := toWeights_injective payload
 refine ⟨child,reply,?_⟩
 cases out;cases child;cases address;cases same;rfl

#print axioms mapArray_injective
#print axioms toQ_injective
#print axioms variant_injective
#print axioms toWeights_injective
#print axioms returned
end AspisR1.NIW_AlignOwner
