import NHG_Product
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1.NHG_FinishLeaves
open AspisR1PublicPreparation.RawExtractedSemanticCallOpsV20
open AspisR1.ExtractedMaskQM31Exact
abbrev Q := AspisR1SemanticCallExtraction.aspis_core.field.QM31
abbrev Canonical (x : Q) := CurrentCanonicalQM (genQToProbe x)
abbrev Coefficients := AspisR1PublicPreparation.RawExtractedSemanticBoundaryLoopV7.coefficients
noncomputable abbrev Polynomial (coeffs : List QM31Exact) := AspisR1PublicPreparation.RawSemanticPolynomialOps.polynomial coeffs

def boundaryBody (p : Array Q 28#usize) (acc : Q) (index : Usize) :
 Result (ControlFlow (Q×Usize) Q) :=
 if index<28#usize then do
  let coefficient←Array.index_usize p index
  let next←AspisR1SemanticCallExtraction.aspis_core.field.QM31.add acc coefficient
  let cursor←index+1#usize
  ok (.cont (next,cursor))
 else ok (.done acc)

theorem boundary_step (p : Array Q 28#usize) (acc : Q) (index : Usize) :
 AspisR1SemanticCallExtraction.r1_semantic.semantic_boundary_loop.body p acc index=
 boundaryBody p acc index := rfl

/-- The seed is coefficient0 AND the forward fold starts at0. The retained
induction therefore adds coefficient0 twice, not once. -/
theorem boundary_seed (p : Array Q 28#usize) :
 AspisR1SemanticCallExtraction.r1_semantic.semantic_boundary p=
 (do let seed←Array.index_usize p 0#usize
     AspisR1SemanticCallExtraction.r1_semantic.semantic_boundary_loop p seed 0#usize) := rfl

theorem boundary_result (p : Array Q 28#usize)
 (canonical : ∀ i (hi : i<28),Canonical (p.val[i]'(by simpa [p.property] using hi))) :
 ∃ out,AspisR1SemanticCallExtraction.r1_semantic.semantic_boundary p=ok out ∧
 Canonical out ∧ decode (genQToProbe out)=(Polynomial (Coefficients p)).eval 0+
  (Polynomial (Coefficients p)).eval 1 :=
 AspisR1PublicPreparation.RawExtractedSemanticPolynomialWrappersV1.semantic_boundary_refines_polynomial_endpoints p canonical

def valueBody (multiply : Q→Q→Result Q) (p : Array Q 28#usize)
 (alpha : Array Q 10#usize) (round index : Usize) (acc : Q) :
 Result (ControlFlow (Usize×Q) Q) :=
 if index>0#usize then do
  let cursor←index-1#usize
  let challenge←Array.index_usize alpha round
  let product←multiply acc challenge
  let coefficient←Array.index_usize p cursor
  let next←AspisR1SemanticCallExtraction.aspis_core.field.QM31.add product coefficient
  ok (.cont (cursor,next))
 else ok (.done acc)

theorem value_step (p : Array Q 28#usize) (alpha : Array Q 10#usize)
 (round index : Usize) (acc : Q) :
 AspisR1SemanticCallExtraction.r1_semantic.semantic_value_loop.body p alpha round index acc=
 valueBody AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul p alpha round index acc := rfl

theorem value_seed (p : Array Q 28#usize) (alpha : Array Q 10#usize) (round : Usize) :
 AspisR1SemanticCallExtraction.r1_semantic.semantic_value p alpha round=
 AspisR1SemanticCallExtraction.r1_semantic.semantic_value_loop p alpha round 28#usize AspisR1SemanticCallExtraction.aspis_core.field.QM31.ZERO := rfl

/-- The existing emitted-loop induction is reused. Multiplication is the
exact paired Product law; no product arithmetic is checked in Kani. -/
theorem value_result (p : Array Q 28#usize) (alpha : Array Q 10#usize) (round : Usize)
 (hround : round.val<10)
 (halpha : ∀ i (hi : i<10),Canonical (alpha.val[i]'(by simpa [alpha.property] using hi)))
 (canonical : ∀ i (hi : i<28),Canonical (p.val[i]'(by simpa [p.property] using hi))) :
 ∃ out,AspisR1SemanticCallExtraction.r1_semantic.semantic_value p alpha round=ok out ∧
 Canonical out ∧ decode (genQToProbe out)=
 (Polynomial (AspisR1PublicPreparation.RawExtractedSemanticValueLoopV1.coefficients p)).eval
  (decode (genQToProbe (alpha.val[round.val]'(by simpa [alpha.property] using hround)))) :=
 AspisR1PublicPreparation.RawExtractedSemanticValueLoopV1.semantic_value_refines_polynomial_eval
  p alpha round hround (halpha round.val hround) canonical

noncomputable def productPacket (a b : Q) : Result Q := by
 classical
 exact if h : Canonical a ∧ Canonical b then
  ok (NHG_Product.reply a b h.1 h.2) else AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul a b

theorem product_packet (a b : Q) : productPacket a b=AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul a b := by
 classical
 unfold productPacket
 split
 · rename_i h
   exact (NHG_Product.returns a b h.1 h.2).symm
 · rfl

theorem value_packet_step (p : Array Q 28#usize) (alpha : Array Q 10#usize)
 (round index : Usize) (acc : Q) :
 AspisR1SemanticCallExtraction.r1_semantic.semantic_value_loop.body p alpha round index acc=
 valueBody productPacket p alpha round index acc := by
 have packet : productPacket=AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul := funext (fun a=>funext (fun b=>product_packet a b))
 rw [packet]
 exact value_step p alpha round index acc

#print axioms product_packet
#print axioms value_packet_step
#print axioms boundary_step
#print axioms boundary_seed
#print axioms boundary_result
#print axioms value_step
#print axioms value_seed
#print axioms value_result
#print FIq_Native.pool_v1.pair_forest_semantic_terminal.selected_claim
end AspisR1.NHG_FinishLeaves
