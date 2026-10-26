import F3K_ConcreteDecode
import F3K_QueryDecoderSource
import R1LiteralQuerySample
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3K_SourceQueryDecode
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisV8R19.Q22SamplerInvariants R0C.V3

theorem concrete (blocks advances : F3K_QueryScanStep.Blocks)
    (out : Array U32 22#usize) (selected : Array U8 32#usize) (initial : State)
    (h : Query31ConcreteMaterializedSchedule.actualConcreteDecode
      Query31ConcreteDriverTraceFacts.sourceDefaultState blocks advances=ok (.Ok (out,selected))) :
    ∃ q,LiteralQueryRead.decode (out.val.map (fun x=>x.val))=some q := by
  have eq := F3K_ConcreteDecode.accepted blocks advances out selected initial h
  have valid := LiteralQuerySample.scanOut_result_valid 8 Q22.q0
    (blocks.val.map decodeState) (advances.val.map decodeState) initial
    (by simp [Valid,Q22.q0])
  rw [eq] at valid
  change (out.val.map (fun x=>x.val)).Nodup ∧ (out.val.map (fun x=>x.val)).length=22 ∧
    ∀ x∈out.val.map (fun x=>x.val),x<262144 at valid
  unfold LiteralQueryRead.decode
  exact ⟨_,dif_pos valid⟩

theorem source {Hash : Type} (D : aspis_core.Digest32 Hash)
    (embed : aspis_core.field.M31 → Result aspis_core.field.WideExact)
    (before after : transcript.Transcript Hash) (payload : Slice U8) (out : Array U32 22#usize)
    (success : QueriesModel.queries (Query31ConcreteMaterializedSchedule.concreteBoundaries
      Query31ConcreteDriverTraceFacts.sourceDefaultState embed) D before 31#u8 payload=ok (.Ok out,after)) :
    ∃ q,LiteralQueryRead.decode (out.val.map (fun x=>x.val))=some q ∧
      ∀ j : Fin 22,(out.val[j.val]'(by have len : out.val.length=22:=out.property;omega)).val=(q j).val := by
  obtain ⟨absorbed,blocks,advances,selected,ha,values,decoded,carried⟩ :=
    F3K_QueryDecoderSource.source _ D before after 31#u8 payload out success
  obtain ⟨q,hq⟩ := concrete blocks advances out selected (decodeState absorbed.state) decoded
  refine ⟨q,hq,?_⟩
  intro j
  have order := (LiteralQueryRead.decode_success _ _ hq).1
  have atIndex := congrArg (fun xs : List Nat=>xs[j.val]?) order
  have hj : j.val<out.val.length := by have len : out.val.length=22:=out.property;omega
  simp only [List.getElem?_ofFn,List.getElem?_map,List.getElem?_eq_getElem hj,Option.map_some,
    dif_pos j.isLt] at atIndex
  exact (Option.some.inj atIndex).symm

#print axioms concrete
#print axioms source
end AspisR1.F3K_SourceQueryDecode
end
