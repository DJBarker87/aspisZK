import NEV_PrimitiveBindings
import NEI_PushBridge
import NEI_PushRawAssociation
import NBF_Progress
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace NEV_PushDomains
open Aeneas Aeneas.Std Result NEV_AccumulateCarriers AspisR1

def bw (b : NEV_AccumulateRaw.BatchedWeights) : NEI_PushBridge.BW := ⟨b.raw,b.terms⟩
def power (q : RawQ) : NEI_PushBridge.Power :=
 NEI_PushRawAssociation.toPower (NEV_AccumulateRaw.NEV_Bindings.toPushQ q)

theorem canonical_limb (q : RawQ) (canonical : NBF_PowerStep.Canonical (toQ q)) (index : Usize) :
    (S7Kani2OwnedRow.limb (NEG_RowBridge.modelPower (power q)) index).val<2147483647 := by
  have words := (NEV_StageFields.canonical_q (toQ q)).mp canonical
  change (if index=0#usize then q.c0.a else if index=1#usize then q.c0.b
    else if index=2#usize then q.c1.a else q.c1.b).val<2147483647
  split_ifs <;> first | exact words.1.1 | exact words.1.2 | exact words.2.1 | exact words.2.2

/-- The reached same-vector progress witness supplies the CLOSED NEI push
packet's exact overflow domain. No stronger row bound or callee success is
assumed. Existing phase_bound proves the final scalar inequality. -/
theorem reached (b : NEV_AccumulateRaw.BatchedWeights) (index : Usize) (q : RawQ) (basis : U32)
    (progress : S7JoinRowsTrace.Progress b.terms.val index.val
      (Port3_RowsInstall.toBW (toWeights b)))
    (inside : index.val<64) (canonical : NBF_PowerStep.Canonical (toQ q))
    (basisCanonical : basis.val<2147483647) :
    NEI_PushBridge.Domain (bw b) index (power q) basis := by
  have size : b.raw.val.length=64 := progress.2.1
  have inRange : index.val<b.raw.val.length := by omega
  have inv := NBF_Progress.sweep b.terms.val index.val (toWeights b) progress
  refine ⟨inRange,?_⟩
  intro row read
  obtain ⟨actual,actualRun,atIndex⟩ := WP.spec_imp_exists
    (alloc.vec.Vec.index_usize_spec b.raw index inRange)
  have given : alloc.vec.Vec.index_usize b.raw index=ok row := read
  have same : actual=row := Result.ok.inj (actualRun.symm.trans given)
  have listed : b.raw.val[index.val]?=some row := by
    rw [List.getElem?_eq_getElem inRange]
    exact congrArg some (atIndex.symm.trans same)
  have bound : NBB_Sweep.Bound b.terms.val row := by
    have current := inv index.val row listed
    simpa only [Nat.lt_irrefl,if_false] using current
  intro lane word laneInside wordRead
  obtain ⟨selected,selectedRun,selectedAt⟩ := WP.spec_imp_exists
    (Array.index_usize_spec row lane (by change lane.val<row.val.length;rw [row.property];exact laneInside))
  have sameWord : selected=word := Result.ok.inj (selectedRun.symm.trans wordRead)
  have member : word∈row.val := by
    have equality : word=row.val[lane.val]'(by rw [row.property];exact laneInside) := sameWord.symm.trans selectedAt
    rw [equality]
    exact List.getElem_mem _
  exact S7OwnedP6ScalarProof.phase_bound word _ basis (b.terms.val%4)
    (Nat.mod_lt _ (by decide)) (canonical_limb q canonical lane) basisCanonical (bound word member)
#print axioms canonical_limb
#print axioms reached
end NEV_PushDomains
end
