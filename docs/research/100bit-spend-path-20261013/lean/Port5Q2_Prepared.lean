import Port4C_Installed
import Port4A_PrepareCut
import Port3_DecodeCoherence

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port5Q2_Prepared
open Aeneas Aeneas.Std Result VTop_Stages
open CheckpointBytes3Namespaces
open OraclePortCkptAbi4Decode OraclePortCkptAbi5Codec

/-- Only immutable preparation fields; contains no accumulator, query result,
writer return or complete checkpoint provenance. -/
structure PreparedFields (p : verifier.Prepared) : Prop where
  variant : p.variant=.S2
  queries : ∀ j : Fin 22,
    (p.queries.val[j.val]'(by simpa [p.queries.property] using j.isLt)).val<262144
  gamma : CanonicalWide (toE p.gamma)
  kappa : CanonicalWide (toE p.kappa)
  alpha : ∀ j : Fin 2, CanonicalWide (toE
    (p.alpha.val[j.val]'(by simpa [p.alpha.property] using j.isLt)))
  rho : Port3_FlushInstall.Canonical p.rho
  semanticAlpha : ∀ j : Fin 10, Canonical (toK
    (p.semantic_alpha.val[j.val]'(by simpa [p.semantic_alpha.property] using j.isLt)))
  coordinates : ∀ j : Fin 4, Canonical (toK (match j.val with
    | 0 => (p.z.val[0]'(by simp [p.z.property])).x
    | 1 => (p.z.val[0]'(by simp [p.z.property])).y
    | 2 => (p.z.val[1]'(by simp [p.z.property])).x
    | _ => (p.z.val[1]'(by simp [p.z.property])).y))
  claim : CanonicalWide (toE p.claim)

/-- Session A's concrete op7 contract, retained as ONE named hypothesis.
The successful return is the prefix's own preparation on its actual zero input.
This does not assert that an arbitrary op7 satisfies the contract. -/
structure SessionAPrepare (base : Ops) : Prop where
  accepted : ∀ {H : Type} (D : aspis_core.digest.Digest32 H) (hash : H)
    (semantic : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) zero g p,
    base.op1=ok zero →
    base.op7 D semantic proof hash none (Array.repeat 29#usize zero)=ok (.Ok p,g) →
    PreparedFields p

variable {CoreError W : Type}

/-- All canonical raw checkpoint fields are derived on the SAME writer input.
Only the immutable fields come from preparation; rhs/power/weights come from
Port4C's same-prefix arithmetic induction, not from this prepare contract. -/
theorem reached (base : Ops) (reserved : Bool) (batch : Port3_NativeBatchBody.Ops)
    (geometry : Port3_NativeGeometryBody.Ops CoreError) (query : Port3_NativeQueryBody.Ops)
    (finish : AspisR1Stage2.Stage2Finish.FinishOps W)
    (prepare : SessionAPrepare base)
    (basis : Port4C_BasisOuter.SessionABasis query)
    (arithmetic : Port4C_QueryArithmetic.SessionABackends query)
    (lineCanonical : ∀ alpha values inverses value,
      query.op16 alpha values inverses=ok value → Port4C_QueryArithmetic.CanonE value)
    {H : Type} (D : aspis_core.digest.Digest32 H) (hash : H)
    (semantic : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (split : Usize) (p : verifier.Prepared) (a : verifier.Accumulator)
    (reached1 : VTop_Provenance.WriterPrefix
      (Port4C_Installed.installed base reserved batch geometry query finish)
      D hash semantic proof split none p a) :
    ∃ fields : PreparedFields p, reserved=true ∧ split.val=10 ∧ a.next.val=10 ∧
    ∃ size : a.weights.val.length=64,
      CheckpointBytesBlocks.CanonicalFields
        (Port3_DecodeCoherence.inventory p a size fields.queries) := by
  obtain ⟨zero,g,hzero,hprep⟩ := Port4A_PrepareCut.returned base reserved batch
    (Port4C_GeometryInverse.install (Port4C_CollectStd.install geometry))
    (Port4C_RowStd.install query) finish D hash semantic proof split p a reached1
  have fields := prepare.accepted D hash semantic proof zero g p hzero hprep
  obtain ⟨hr,hs,hn,size,rhs,power,weights,sum,hsum⟩ :=
    Port4C_Installed.writer_fields base reserved batch geometry query finish basis arithmetic
      lineCanonical D hash semantic proof split p a fields.rho reached1
  refine ⟨fields,hr,hs,hn,size,?_⟩
  refine ⟨fields.gamma,fields.kappa,?_,fields.rho,?_,?_,fields.claim,rhs,power,?_⟩
  · simpa only [Port3_DecodeCoherence.inventory,CheckpointBytesBody.fields,
      toPrepared,mapArray,List.getElem_map] using fields.alpha
  · simpa only [Port3_DecodeCoherence.inventory,CheckpointBytesBody.fields,
      toPrepared,mapArray,List.getElem_map] using fields.semanticAlpha
  · intro j
    have hc := fields.coordinates j
    fin_cases j <;>
      simpa only [Port3_DecodeCoherence.inventory,CheckpointBytesBody.fields,
        toPrepared,mapArray,List.getElem_map,toPoint] using hc
  ·
    intro j
    simp only [Port3_DecodeCoherence.inventory,CheckpointBytesBody.fields,toAccumulator,
      mapVec,List.getElem_map]
    exact weights _ (List.getElem_mem _)

#print axioms reached
end AspisR1.Port5Q2_Prepared
end
