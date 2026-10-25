import WAdm_FissionedContent
import WAdm_SourceBody
import WAdm_Append
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.WAdm_FissionedFields
open WAdm_Fissioned WAdm_model
open OraclePortCkptAbi2Extracted.aspis_r1_cost_probe.verifier

def fields (p : Prepared) (a : Accumulator) : WAdm_Fields where
  roots := p.roots
  state := p.state
  early := Array.make 4#usize [p.gamma,p.kappa,
    p.alpha.val[0]'(by simp [p.alpha.property]),p.alpha.val[1]'(by simp [p.alpha.property])]
  rho := p.rho
  queries := p.queries
  semantic := p.semantic_alpha
  coordinates := Array.make 4#usize [
    (p.z.val[0]'(by simp [p.z.property])).x,(p.z.val[0]'(by simp [p.z.property])).y,
    (p.z.val[1]'(by simp [p.z.property])).x,(p.z.val[1]'(by simp [p.z.property])).y]
  tail := Array.make 2#usize [p.claim,a.rhs]
  power := a.power

theorem returned (p : Prepared) (a : Accumulator) :
    WAdm_fields p a.rhs a.power = ok (fields p a) := by
  simp (disch := scalar_tac) [WAdm_fields,fields,Array.index_usize,p.alpha.property,p.z.property,lift]

theorem body_bytes (p : Prepared) (a : Accumulator) (hp hu : Array U8 32#usize)
    (variant : p.variant = .S2) (next : a.next.val = 10) :
    MultiproofConeCanonical.bytesOf (WAdm_FissionedContent.body (fields p a) a.weights hp hu) =
      WAdm_SourceBody.body p a hp hu := by
  have zpair := congrArg
    (List.flatMap (fun z : OraclePortCkptAbi2Extracted.aspis_core.circle.SecureCirclePoint =>
      WAdm_SourceBody.putK z.x ++ WAdm_SourceBody.putK z.y)) (WAdm_SourceBody.two p.z)
  unfold WAdm_SourceBody.body
  rw [variant,CheckpointBytesHeader.next_cast a.next next,WAdm_Append.alpha,zpair]
  simp only [WAdm_FissionedContent.body,fields,WAdm_FissionedContent.header,
    WAdm_SourceBody.put,WAdm_SourceBody.putK,CheckpointBytesBlocks.rawK,
    MultiproofConeCanonical.bytesOf,List.map_append,List.map_flatMap,
    Array.make,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.map_cons,List.map_nil,
    WAdm_SourceBody.tag,List.append_assoc]
  rfl

#print axioms returned
#print axioms body_bytes
end AspisR1.WAdm_FissionedFields
end
