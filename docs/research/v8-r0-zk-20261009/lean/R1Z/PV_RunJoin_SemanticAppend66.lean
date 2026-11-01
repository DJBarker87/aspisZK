import R1Z.PV_RunJoin_SemanticDomainBound66
import R1Z.PV_RunJoin_SemanticComplete40
import R1Z.PV_RunJoin_ActualPlanSources59
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SemanticAppend66
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_PublishSkeleton54
variable [ExternalTypes]
theorem complete (ops : ExternalFuns) (fixed : ProverRwP6BodyCandidate.selected ops=ops)
    (logical : Slice U8) (records : List (List U8)) (length : logical.length=13831)
    (domain : PV_RunJoin_SemanticDomain40.Domain ops logical 27#u8 32#usize 0#u8 records) :
    ∃ encoded, @host_compact.compact_semantic _ ops logical PV_RunJoin_ActualPlanSources59.empty=ok (.Ok (),encoded) ∧
      ∀ out : alloc.vec.Vec U8, out.length+(bytes encoded.val).length≤Usize.max →
        ∃ next, @host_compact.compact_semantic _ ops logical out=ok (.Ok (),next) ∧
          bytes next.val=bytes out.val++bytes encoded.val := by
  have bound := PV_RunJoin_SemanticDomainBound66.complete ops logical 27#u8 32#usize 0#u8 records domain
  have cap : 13831≤Usize.max := by clear fixed domain bound length logical records ops;scalar_tac
  have emptylen : PV_RunJoin_ActualPlanSources59.empty.length=0 := rfl
  obtain ⟨encoded,he,hv⟩ := PV_RunJoin_SemanticComplete40.encode ops logical
    PV_RunJoin_ActualPlanSources59.empty records length domain (by change 0+32+records.flatten.length≤Usize.max;change 32+records.flatten.length≤logical.length at bound;omega)
  rw [fixed] at he
  refine ⟨encoded,he,?_⟩
  intro out room
  have le : (bytes encoded.val).length=32+records.flatten.length := by
    change (encoded.val.map _).length=_
    rw [List.length_map,hv,List.length_append,List.length_append,List.length_take]
    change 0+min 32 logical.length+records.flatten.length=_
    rw [length];omega
  have available : out.length+32+records.flatten.length≤Usize.max := by rw [le] at room;omega
  obtain ⟨next,hn,hnv⟩ := PV_RunJoin_SemanticComplete40.encode ops logical out records length domain available
  rw [fixed] at hn
  refine ⟨next,hn,?_⟩
  simp only [bytes,hnv,hv,PV_RunJoin_ActualPlanSources59.empty,List.nil_append,List.map_append]
#print axioms complete
end R1Z.PV_RunJoin_SemanticAppend66
