import TxS_Prepared
import Tx2N_Fields
set_option autoImplicit false
noncomputable section
namespace AspisR1.TxS_Transfer
open Aeneas Aeneas.Std Result AspisR1Stage2
open OraclePortCheckpointAbiC5

theorem prepare (source target : verifier.Prepared) (old fresh : verifier.Accumulator)
    (size : old.weights.val.length=64)
    (qb : ∀ j : Fin 22,(source.queries.val[j.val]'(by have h : source.queries.val.length=22:=source.queries.property;omega)).val<262144)
    (canonical : CheckpointBytesBlocks.CanonicalFields (Port3_DecodeCoherence.inventory source old size qb))
    (am : QueryAccumulator.State K E)
    (fields : CheckpointBytes4SavedFields.BodyMatches target fresh
      (CheckpointBytesBlocks.prepared (Port3_DecodeCoherence.inventory source old size qb) canonical) am)
    (data : MatchingSupport.Data E) (rho : K) (q : Fin 22 → Fin 262144)
    (port : Port5Q1_QueryPorts.SessionAPrepare source data q rho) :
    Port5Q1_QueryPorts.SessionAPrepare target data q rho ∧
    fresh.weights.val.length=64 ∧ Port3_FlushInstall.Canonical fresh.power ∧
    Port4C_QueryArithmetic.CanonE fresh.rhs := by
  obtain ⟨rhoEq,queriesEq,alphaEq⟩ := TxS_Prepared.fields source old size qb canonical
  refine ⟨⟨?_,?_,?_,?_⟩,?_,?_,?_⟩
  · intro j hj
    have mapped := congrArg (fun xs : List Nat => xs[j]?) fields.queries
    have qs : (CheckpointBytesBlocks.prepared (Port3_DecodeCoherence.inventory source old size qb) canonical).queries=q := by
      rw [queriesEq]
      funext k
      apply Fin.ext
      have bound : k.val<source.queries.val.length := by have h : source.queries.val.length=22:=source.queries.property;omega
      have cell := port.queries k.val k.isLt
      simp only [CheckpointBytes5Output.queries,List.getElem?_map,List.getElem?_eq_getElem bound,
        Option.map_some,Option.getD_some]
      have eq : (source.queries.val[k.val]'bound).val=(q k).val := by
        simpa only [Port5Q1_GeometryBinding.queryAt,List.getElem?_eq_getElem bound,Option.getD_some] using cell
      rw [eq,Nat.mod_eq_of_lt (q k).isLt]
    rw [qs] at mapped
    simp only [List.getElem?_map,List.getElem?_ofFn,hj,↓reduceDIte] at mapped
    have room : j<target.queries.val.length := by have h : target.queries.val.length=22:=target.queries.property;omega
    simpa only [Port5Q1_GeometryBinding.queryAt,List.getElem?_eq_getElem room,
      Option.map_some,Option.getD_some,Option.some.injEq] using mapped
  · rw [fields.rho,CheckpointBytes5Output.ofK_source,rhoEq,port.rho_eq]
  · rw [fields.rho]; exact Tx2N_Fields.canonical_k _
  · intro alpha read
    have at1 : Array.index_usize target.alpha 1#usize=ok
      (CheckpointBytes4ReaderFields.sourceE
        ((CheckpointBytesBlocks.prepared (Port3_DecodeCoherence.inventory source old size qb) canonical).alpha 1)) := by
      simp [Array.index_usize,fields.alpha]
    have eq := Result.ok.inj (read.symm.trans at1)
    rw [eq,CheckpointBytes5Output.ofE_source,alphaEq]
    apply port.alpha1
    simp [Array.index_usize]
  · rw [fields.weights,List.length_map,List.length_ofFn]
  · rw [fields.power]; exact Tx2N_Fields.canonical_k _
  · rw [fields.rhs]; exact Tx2N_Fields.canonical_e _

#print axioms prepare
end AspisR1.TxS_Transfer
end
