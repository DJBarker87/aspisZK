import NIX_SamplerLaw
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIX_ValidatedCut
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open PreparedHashCode (Code)

/-- The exact returning/error continuation transcribed from the native
circle_validated local records. Child post-state is retained even on Err. -/
def after {H : Type} (B : FinishModel.Boundaries) (row : FinishModel.CircleRow)
 (self : r1_wire.SemanticTranscript H)
 (r : core.result.Result (Array U8 32#usize) r1_wire.Error) :
 Code ((core.result.Result aspis_core.circle.SecureCirclePoint r1_wire.Error) × r1_wire.SemanticTranscript H) := do
 let cf←core.result.Result.Insts.CoreOpsTry.branch r
 match cf with
 | .Continue block=>
   let point←B.circle block row
   pure (.Ok point,self)
 | .Break residual=>
   let r1←core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
    aspis_core.circle.SecureCirclePoint (core.convert.FromSame r1_wire.Error) residual
   pure (r1,self)

def dispatch {H : Type} (B : FinishModel.Boundaries) (D : aspis_core.Digest32 H)
 (self : r1_wire.SemanticTranscript H) (record : r1_wire.ValidatedRecord) (row : U8) :
 Code ((core.result.Result aspis_core.circle.SecureCirclePoint r1_wire.Error) × r1_wire.SemanticTranscript H) := do
 match row with
 | 25#uscalar=>
   let frame←r1_wire.ValidatedRecord.impl.framed record
   let (r,post)←S1SemanticCode.sampleBlock D self 25#u8 frame
   after B .First post r
 | 26#uscalar=>
   let frame←r1_wire.ValidatedRecord.impl.framed record
   let (r,post)←S1SemanticCode.sampleBlock D self 26#u8 frame
   after B .Second post r
 | _=>pure (.Err .InvalidRow,self)

def cut {H : Type} (B : FinishModel.Boundaries) (D : aspis_core.Digest32 H)
 (self : r1_wire.SemanticTranscript H) (record : r1_wire.ValidatedRecord) :
 Code ((core.result.Result aspis_core.circle.SecureCirclePoint r1_wire.Error) × r1_wire.SemanticTranscript H) := do
 let row←r1_wire.ValidatedRecord.impl.row record
 dispatch B D self record row

/-- Native G with each logged reply replaced by its packet is this SAME
adopted emitted driver, preserving the full Code (therefore ordered effects). -/
theorem source {H : Type} (B : FinishModel.Boundaries) (D : aspis_core.Digest32 H)
 (self : r1_wire.SemanticTranscript H) (record : r1_wire.ValidatedRecord) :
 cut B D self record=S1SemanticCode.circleValidated B D self record := rfl

/-- No sampler is called after a returned block error, for either valid row. -/
theorem error_no_suffix {H : Type} (B C : FinishModel.Boundaries) (row : FinishModel.CircleRow)
 (self : r1_wire.SemanticTranscript H) (error : r1_wire.Error) :
 PreparedHashCode.run (after B row self (.Err error))=
 PreparedHashCode.run (after C row self (.Err error)) := rfl

/-- The two Rust match cases establish the sampler's complete row domain. -/
theorem row_cases (row : U8) :
 row=25#u8 ∨ row=26#u8 ∨ (row≠25#u8 ∧ row≠26#u8) := by
 by_cases a : row=25#u8
 · exact .inl a
 · by_cases b : row=26#u8
   · exact .inr (.inl b)
   · exact .inr (.inr ⟨a,b⟩)

#print axioms source
#print axioms error_no_suffix
#print axioms row_cases
end AspisR1.NIX_ValidatedCut
end
