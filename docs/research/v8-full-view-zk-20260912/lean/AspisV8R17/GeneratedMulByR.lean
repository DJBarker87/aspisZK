import AspisV8R17.GeneratedCM31Linear

namespace V7Tag73CurrentHelpersOpaque
open Aeneas Aeneas.Std Result
-- GENERATED FunsChunk04.lean
@[rust_fun "aspis_core::field::mul_by_r"]
def aspis_core.field.mul_by_r
  (x : aspis_core.field.CM31) : Result aspis_core.field.CM31 := do
  let m ← aspis_core.field.M31.double x.a
  let m1 ← aspis_core.field.M31.sub m x.b
  let m2 ← aspis_core.field.M31.double x.b
  let m3 ← aspis_core.field.M31.add x.a m2
  ok { a := m1, b := m3 }
-- END GENERATED
end V7Tag73CurrentHelpersOpaque

namespace AspisV8R17.GeneratedMulByR
open Aeneas.Std V7Tag73CurrentHelpersOpaque RawReducer GeneratedCM31Linear

theorem generated_words (x : aspis_core.field.CM31) (hx : Canonical x) :
    ∃ z, aspis_core.field.mul_by_r x = .ok z ∧ Canonical z ∧
      z.a.val = ((x.a.val+x.a.val)%P+P-x.b.val)%P ∧
      z.b.val = (x.a.val+(x.b.val+x.b.val)%P)%P := by
  obtain ⟨a2, ea2, va2, ca2⟩ := GeneratedM31Add.generated_double_mod x.a hx.1
  obtain ⟨a, ea, va, ca⟩ := GeneratedM31Sub.generated_sub_mod a2 x.b ca2 hx.2
  obtain ⟨b2, eb2, vb2, cb2⟩ := GeneratedM31Add.generated_double_mod x.b hx.2
  obtain ⟨b, eb, vb, cb⟩ := GeneratedM31Add.generated_add_mod x.a b2 hx.1 cb2
  refine ⟨⟨a,b⟩, ?_, ⟨ca,cb⟩, ?_, ?_⟩
  · simp only [aspis_core.field.mul_by_r, ea2, ea, eb2, eb, bind_tc_ok]
  · simpa only [va2] using va
  · simpa only [vb2] using vb

theorem real_residue (a b : Nat) (hb : b<P) :
    ((((a+a)%P+P-b)%P : Nat) : Int) =
      ((a : Int)+(a : Int)-(b : Int))%(P : Int) := by
  unfold P at *
  omega

theorem imag_residue (a b : Nat) :
    (a+(b+b)%P)%P = (a+b+b)%P := by
  unfold P
  omega

theorem generated_residues (x : aspis_core.field.CM31) (hx : Canonical x) :
    ∃ z, aspis_core.field.mul_by_r x = .ok z ∧ Canonical z ∧
      (z.a.val : Int) = ((x.a.val : Int)+(x.a.val : Int)-(x.b.val : Int))%(P : Int) ∧
      z.b.val = (x.a.val+x.b.val+x.b.val)%P := by
  obtain ⟨z, ez, cz, va, vb⟩ := generated_words x hx
  refine ⟨z, ez, cz, ?_, ?_⟩
  · rw [va]; exact real_residue _ _ hx.2
  · rw [vb]; exact imag_residue _ _

#print axioms generated_words
#print axioms real_residue
#print axioms imag_residue
#print axioms generated_residues
end AspisV8R17.GeneratedMulByR
