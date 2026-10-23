import Port3_WriterShape

/-! Coherence of checkpoint's canonical raw inventory with the very same
total numeric decoder used for query states. No completed model state is
chosen or postulated by these carrier identities. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port3_DecodeCoherence
open Aeneas Aeneas.Std
open CheckpointBytes3Namespaces
open OraclePortCkptAbi4Decode OraclePortCkptAbi5Codec

theorem k_decode (q : AspisR1Stage2.aspis_core.field.QM31)
    (h : Canonical (toK q)) :
    exactK (toK q) h = CheckpointBytes5Output.ofK q := by
  unfold exactK CheckpointBytes5Output.ofK
  congr 1
  funext j
  apply Fin.ext
  fin_cases j
  · change q.c0.a.val = q.c0.a.val % 2147483647
    exact (Nat.mod_eq_of_lt h.1).symm
  · change q.c0.b.val = q.c0.b.val % 2147483647
    exact (Nat.mod_eq_of_lt h.2.1).symm
  · change q.c1.a.val = q.c1.a.val % 2147483647
    exact (Nat.mod_eq_of_lt h.2.2.1).symm
  · change q.c1.b.val = q.c1.b.val % 2147483647
    exact (Nat.mod_eq_of_lt h.2.2.2).symm

theorem e_decode (q : AspisR1Stage2.aspis_core.field.wide_exact.WideExact)
    (h : CanonicalWide (toE q)) :
    exactE (toE q) h = CheckpointBytes5Output.ofE q := by
  change (⟨exactK (toK q.c0) h.1,exactK (toK q.c1) h.2⟩ : OraclePortCheckpointAbiC5.E) = _
  rw [k_decode,k_decode]
  rfl


def inventory (p : AspisR1Stage2.verifier.Prepared) (a : AspisR1Stage2.verifier.Accumulator)
    (size : a.weights.val.length=64)
    (qb : ∀ j : Fin 22, (p.queries.val[j.val]'(by simpa [p.queries.property] using j.isLt)).val<262144) :=
  CheckpointBytesBody.fields (toPrepared p) (toAccumulator a)
    (by simpa [toAccumulator,mapVec] using size) qb

theorem accumulator_coherent (p : AspisR1Stage2.verifier.Prepared)
    (a : AspisR1Stage2.verifier.Accumulator) (size : a.weights.val.length=64)
    (qb : ∀ j : Fin 22, (p.queries.val[j.val]'(by simpa [p.queries.property] using j.isLt)).val<262144)
    (canonical : CheckpointBytesBlocks.CanonicalFields (inventory p a size qb))
    (next : a.next.val=10) :
    CheckpointBytesBlocks.accumulator (inventory p a size qb) canonical =
      CheckpointBytes5Output.accumulator a := by
  unfold CheckpointBytesBlocks.accumulator CheckpointBytes5Output.accumulator
  congr 1
  · funext j
    have hi : j.val<a.weights.val.length := by rw [size]; exact j.isLt
    simp only [inventory,CheckpointBytesBody.fields,toAccumulator,mapVec,List.getElem_map]
    rw [List.getElem?_eq_getElem hi,Option.getD_some]
    have hc : Canonical (toK (a.weights.val[j.val]'(hi))) := by
      simpa only [inventory,CheckpointBytesBody.fields,toAccumulator,mapVec,List.getElem_map] using canonical.weights j
    exact k_decode _ hc
  · exact e_decode _ canonical.rhs
  · exact k_decode _ canonical.power
  · exact next.symm


/-- A checkpoint provenance witness necessarily denotes the SAME physical
accumulator. It cannot choose a second mathematical accumulator. This says
nothing yet about equality of that accumulator to the ten-step advance. -/
theorem provenance_state (p : AspisR1Stage2.verifier.Prepared)
    (a : AspisR1Stage2.verifier.Accumulator)
    (pm : OraclePortCheckpointAbiC5.Prepared)
    (am : QueryAccumulator.State OraclePortCheckpointAbiC5.K OraclePortCheckpointAbiC5.E)
    (provenance : CheckpointBytes5Join.S1S7S8StateProvenance (toPrepared p) (toAccumulator a) pm am) :
    am = CheckpointBytes5Output.accumulator a := by
  have size : a.weights.val.length=64 := by
    simpa only [toAccumulator,mapVec,List.length_map] using provenance.size
  have canonical : CheckpointBytesBlocks.CanonicalFields (inventory p a size provenance.queriesBound) := provenance.canonical
  exact provenance.accumulator.symm.trans
    (accumulator_coherent p a size provenance.queriesBound canonical provenance.next)

#print axioms k_decode
#print axioms e_decode
#print axioms accumulator_coherent
#print axioms provenance_state
end AspisR1.Port3_DecodeCoherence
end
