import NFQ_STAGE2_IMPORT
set_option autoImplicit false
namespace NFT_Square
open Aeneas Aeneas.Std Result
abbrev C := AspisR1SelectedMaskProbe.field.CM31
abbrev Canonical := AspisR1.ExtractedMaskTowerAdd.CanonicalCM

def G (wide scalar : Nat) : Nat × Nat :=
  (wide%2147483647,(scalar+scalar)%2147483647)

theorem source (x : C) (canonical : Canonical x) :
    ∃ z : C, AspisR1SelectedMaskProbe.field.CM31.square x=ok z ∧ Canonical z ∧
      (z.a.val,z.b.val)=G ((x.a.val+x.b.val)*(x.a.val+2147483647-x.b.val))
        ((x.a.val*x.b.val)%2147483647) := by
  obtain ⟨z,run,domain,real,imag⟩ := AspisR1.ExtractedMaskCM31Square.current_square_words x canonical
  exact ⟨z,run,domain,by simpa only [G,real,imag]⟩

/-- Total exact value law paired with the abstracted primitive U64 product site. -/
theorem wide_product (x : C) (canonical : Canonical x) :
    ∃ product : U64, AspisR1.ExtractedMaskCM31Square.squareOperand x.a x.b=ok product ∧
      product.val=(x.a.val+x.b.val)*(x.a.val+2147483647-x.b.val) :=
  AspisR1.ExtractedMaskCM31Square.squareOperand_success x.a x.b canonical.1 canonical.2

/-- Total exact value law paired with the opaque M31 product site. -/
theorem scalar_product (a b : U32) :
    ∃ z, AspisR1SelectedMaskProbe.field.M31.mul a b=ok z ∧
      z.val=(a.val*b.val)%2147483647 ∧ z.val<2147483647 :=
  AspisR1.ExtractedMaskReducer.current_mul_mod a b

#print axioms source
#print axioms wide_product
#print axioms scalar_product
end NFT_Square
