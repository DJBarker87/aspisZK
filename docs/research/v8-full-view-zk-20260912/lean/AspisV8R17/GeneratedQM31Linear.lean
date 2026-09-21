import AspisV8R17.GeneratedQM31Products

namespace V7Tag73CurrentHelpersOpaque
open Aeneas Aeneas.Std Result
-- GENERATED FunsChunk04.lean
@[rust_fun "aspis_core::field::{aspis_core::field::QM31}::sub"]
def aspis_core.field.QM31.sub
  (self : aspis_core.field.QM31) (rhs : aspis_core.field.QM31) :
  Result aspis_core.field.QM31
  := do
  let c ← aspis_core.field.CM31.sub self.c0 rhs.c0
  let c1 ← aspis_core.field.CM31.sub self.c1 rhs.c1
  ok { c0 := c, c1 }
-- END GENERATED

-- GENERATED FunsChunk04.lean
@[rust_fun "aspis_core::field::{aspis_core::field::QM31}::add"]
def aspis_core.field.QM31.add
  (self : aspis_core.field.QM31) (rhs : aspis_core.field.QM31) :
  Result aspis_core.field.QM31
  := do
  let c ← aspis_core.field.CM31.add self.c0 rhs.c0
  let c1 ← aspis_core.field.CM31.add self.c1 rhs.c1
  ok { c0 := c, c1 }
-- END GENERATED
end V7Tag73CurrentHelpersOpaque

namespace AspisV8R17.GeneratedQM31Linear
open Aeneas.Std V7Tag73CurrentHelpersOpaque GeneratedQM31Products
open GeneratedQM31Scalar

def qmAddWords (x y : WordPair × WordPair) :=
  (addWords x.1 y.1, addWords x.2 y.2)
def qmSubWords (x y : WordPair × WordPair) :=
  (subWords x.1 y.1, subWords x.2 y.2)

theorem generated_add_words (x y : aspis_core.field.QM31)
    (hx : Canonical x) (hy : Canonical y) :
    ∃ z, aspis_core.field.QM31.add x y = .ok z ∧ Canonical z ∧
      qmWords z = qmAddWords (qmWords x) (qmWords y) := by
  obtain ⟨a, ea, ca, va, wa⟩ := GeneratedCM31Linear.generated_add_words x.c0 y.c0 hx.1 hy.1
  obtain ⟨b, eb, cb, vb, wb⟩ := GeneratedCM31Linear.generated_add_words x.c1 y.c1 hx.2 hy.2
  refine ⟨⟨a,b⟩, ?_, ⟨ca,cb⟩, ?_⟩
  · simp only [aspis_core.field.QM31.add, ea, eb, bind_tc_ok]
  · exact Prod.ext (Prod.ext va wa) (Prod.ext vb wb)

theorem generated_sub_words (x y : aspis_core.field.QM31)
    (hx : Canonical x) (hy : Canonical y) :
    ∃ z, aspis_core.field.QM31.sub x y = .ok z ∧ Canonical z ∧
      qmWords z = qmSubWords (qmWords x) (qmWords y) := by
  obtain ⟨a, ea, ca, va, wa⟩ := GeneratedCM31Linear.generated_sub_words x.c0 y.c0 hx.1 hy.1
  obtain ⟨b, eb, cb, vb, wb⟩ := GeneratedCM31Linear.generated_sub_words x.c1 y.c1 hx.2 hy.2
  refine ⟨⟨a,b⟩, ?_, ⟨ca,cb⟩, ?_⟩
  · simp only [aspis_core.field.QM31.sub, ea, eb, bind_tc_ok]
  · exact Prod.ext (Prod.ext va wa) (Prod.ext vb wb)

#print axioms generated_add_words
#print axioms generated_sub_words
end AspisV8R17.GeneratedQM31Linear
