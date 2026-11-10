import NFS_AccumInstall
import NFS_QueryOps
import NFS_QueryInvariant
import NBF_RowsTotal
import NJJ_QueryOps

/-! NPH_ (R22, item 1 of the 2026-11-10 continuation: the accumulator/cadence family).
Lemmas about the existing gate definitions; nothing merged changes.

The accumulator/cadence invariant is the closure's def predicate
`S7JoinRowsTrace.Progress t 0 (toBW b)` (every one of the 64 residue rows of the
batched-weights state has the per-row phase of term count t: S7Kani3PhaseInvariant.Phase),
together with the numeric fields of NFS_NEV_AccumPacket.Domain (accumulator width 64, raw
length 64, global counter a.next < 22, local term count b.terms < 22, canonical power, rho,
rhs and value). It is established at the state producers by the closure: the pending
constructor (NBF_FirstRows.constructor_progress, Progress 0 0) and, at every reached query
state, NFS_QueryInvariant.Domain (preserved by NFS_QueryInvariant.step; reached states by
NPH_R22JoinCW2.reach_domain on tx2 and NFS_PacketRoot.Domain.invariant on tx1). Push/flush
preservation of Progress is NBF_Progress.body / S7Kani3CallerStep.push_caller_invariant (one
push per row per accumulate call, flush on terms % 4 = 3), used inside NBF_RowsTotal.

Proved here:
- `rows_total`: on that predicate the checked NEV_AccumulateRaw basis producer and 64-row
  weights loop (accumulate_batched_with_node_loop0 with its inner loop, and loop1 with
  BatchedWeights.push → NEI_PushRaw.update_residue_row and both residue loops) return ok,
  with the term count unchanged. Route: NFS_NEV_BasisProducer.total (every node),
  NBF_RowsTotal.full (Progress, canonical power, canonical basis) and
  NFS_NEV_RowLoop.association (raw loop1 = model loop1, no success premise).
- `tail_total`: the checked counter updates terms + 1 and a.next + 1 and the three field
  callees are ok when both counters are < 22 and the operands canonical.
- `acc_total`: NEV_AccumulateRaw.accumulate_batched_with_node is ok on
  NFS_NEV_AccumPacket.Domain, for every node.
- `acc_site`: at every query state satisfying NFS_QueryInvariant.Domain with a.next < finish
  ≤ 22 and a canonical value, the raw accumulate call made by the installed accumulate is ok;
  `installed_ok`: the executed accumulate of NFS_QueryOps.installed is ok there.
Since the whole call is ok, every execution of its loop bodies, of BatchedWeights.push and of
the two update_residue_row loop bodies inside that call is ok, so every checked operation they
execute succeeds and the wrapping reading equals the checked result. Standard axioms. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.NPH_R22Accum
open Aeneas Aeneas.Std Result NEV_AccumulateCarriers AspisR1Stage2

theorem uadd (x y : Usize) (h : x.val + y.val ≤ 65536) :
    ∃ z, (x + y : Result Usize) = ok z ∧ z.val = x.val + y.val := by
  obtain ⟨z, hz, hv⟩ := WP.spec_imp_exists (UScalar.add_spec (x:=x) (y:=y) (by scalar_tac))
  exact ⟨z, hz, by simpa using hv⟩

/-- The raw prefix is the basis producer followed by the 64-row weights loop. -/
theorem rows_cut (a : NEV_AccumulateRaw.Accumulator) (node : U32)
    (b : NEV_AccumulateRaw.BatchedWeights) (width : a.weights.val.length = 64) :
    NFS_NEV_AccumulateTail.rows a node b =
      (do let basis ← NFS_NEV_BasisProducer.source node
          NEV_AccumulateRaw.accumulate_batched_with_node_loop1
            {start:=0#usize,«end»:=64#usize} a.weights a.power a.next b 64#usize basis) := by
  have rawWidth : alloc.vec.Vec.len a.weights = 64#usize := UScalar.eq_of_val_eq width
  unfold NFS_NEV_AccumulateTail.rows NFS_NEV_BasisProducer.source
  rw [rawWidth]
  simp only [NEV_AccumulateRaw.aspis_core.field.M31.ZERO,
    NEV_AccumulateRaw.aspis_core.field.M31.ONE, bind_tc_ok, bind_assoc_eq]

/-- The checked basis loops and the checked 64-row weights loop (push and residue loops
included) are ok on the cadence predicate; the term count is unchanged. -/
theorem rows_total (ops : Port3_NativeQueryBody.Ops) (a : NEV_AccumulateRaw.Accumulator)
    (node : U32) (b : NEV_AccumulateRaw.BatchedWeights)
    (width : a.weights.val.length = 64) (raw : b.raw.val.length = 64) (global : a.next.val < 22)
    (progress : S7JoinRowsTrace.Progress b.terms.val 0 (Port3_RowsInstall.toBW (toWeights b)))
    (hp : NBF_PowerStep.Canonical (toQ a.power)) :
    ∃ mid, NFS_NEV_AccumulateTail.rows a node b = ok mid ∧ mid.terms = b.terms := by
  obtain ⟨basis, hbasis, _⟩ := NFS_NEV_BasisProducer.total ops node
  have hs : NBF_BasisDomain.source ops node = ok basis :=
    (NFS_NEV_BasisProducer.association ops node).symm.trans hbasis
  have hb : ∀ j : Usize, j.val < 64 → ∀ m, Array.index_usize basis j = ok m → m.val < 2^31-1 := by
    intro j hj m read
    exact NBF_BasisDomain.read_canonical ops node basis hs j (by omega) m read
  have v64 : (mapVec toQ a.weights).val.length = 64 := by
    simpa only [mapVec, List.length_map] using width
  obtain ⟨out, run, terms, _, _⟩ := NBF_RowsTotal.full ops (mapVec toQ a.weights) (toQ a.power)
    a.next basis (toWeights b) v64 progress hp hb
  have assoc := NFS_NEV_RowLoop.association ops a.weights a.power a.next basis 64
    {start:=0#usize,«end»:=64#usize} b width raw rfl rfl global
  rw [run] at assoc
  obtain ⟨mid, hmid, hk⟩ := AspisR1.Port3_PushFrame.bind_success _ _ _ assoc
  have same : toWeights mid = out := Result.ok.inj hk
  refine ⟨mid, ?_, ?_⟩
  · rw [rows_cut a node b width, hbasis, bind_tc_ok]
    exact hmid
  · have h1 : (toWeights mid).terms = (toWeights b).terms := by rw [same]; exact terms
    exact h1

/-- The checked counter updates and the field callees of the tail are ok. -/
theorem tail_total (p : NEV_AccumulateRaw.Prepared) (a : NEV_AccumulateRaw.Accumulator)
    (value : RawE) (middle : NEV_AccumulateRaw.BatchedWeights)
    (hterms : middle.terms.val < 22) (global : a.next.val < 22)
    (hv : NBO_TailDomain.WideCanonical (toE value))
    (hr : NBO_TailDomain.WideCanonical (toE a.rhs))
    (hp : NBF_PowerStep.Canonical (toQ a.power))
    (hq : NBF_PowerStep.Canonical (toQ p.rho)) :
    ∃ out, NFS_NEV_AccumulateTail.tail p a value middle = ok out := by
  obtain ⟨t, ht, _⟩ := uadd middle.terms 1#usize (by scalar_tac)
  obtain ⟨product, hprod, cprod⟩ := NFS_NEV_PrimitiveBindings.product_returns value a.power hv hp
  obtain ⟨rhs, hrhs, _⟩ := NFS_NEV_PrimitiveTotal.add a.rhs product hr cprod
  obtain ⟨power, hpow, _⟩ := NFS_NEV_PrimitiveTotal.power a.power p.rho hp hq
  obtain ⟨n, hn, _⟩ := uadd a.next 1#usize (by scalar_tac)
  exact ⟨_, by simp only [NFS_NEV_AccumulateTail.tail, ht, hprod, hrhs, hpow, hn,
    NEV_AccumulateRaw.trace.value, bind_tc_ok]⟩

/-- The whole checked accumulate is ok on the packet domain, for every node. -/
theorem acc_total (p : NEV_AccumulateRaw.Prepared) (a : NEV_AccumulateRaw.Accumulator)
    (node : U32) (value : RawE) (b : NEV_AccumulateRaw.BatchedWeights)
    (d : NFS_NEV_AccumPacket.Domain p a value b) :
    ∃ out, NEV_AccumulateRaw.accumulate_batched_with_node p a node value b = ok out := by
  obtain ⟨mid, hmid, hterms⟩ := rows_total NJJ_QueryOps.concrete a node b d.width
    (NFS_NEV_AccumPacket.raw_length _ _ _ _ d) d.global d.progress d.powerCanonical
  obtain ⟨out, hout⟩ := tail_total p a value mid (by rw [hterms]; exact d.localActive) d.global
    d.valueCanonical d.rhsCanonical d.powerCanonical d.rhoCanonical
  exact ⟨out, by rw [NFS_NEV_AccumulateTail.source_cut, hmid, bind_tc_ok]; exact hout⟩

/-- Caller join: at every query state of the query invariant (inside the loop guard), the raw
accumulate call made by the installed accumulate (NFS_AccumInstall.run) is ok. -/
theorem acc_site {p : verifier.Prepared} {start finish : Nat} {a : verifier.Accumulator}
    {b : verifier.BatchedWeights} (d : AspisR1.NFS_QueryInvariant.Domain p start finish a b)
    (limit : finish ≤ 22) (inside : a.next.val < finish) (node : U32) (value : NFP_QueryCuts.E)
    (canonical : NBO_TailDomain.WideCanonical value) :
    ∃ out, NEV_AccumulateRaw.accumulate_batched_with_node (fromPrepared p) (fromAccumulator a)
      node (fromE value) (fromWeights b) = ok out :=
  acc_total _ _ node _ _ (AspisR1.NFS_AccumDomain.domain p a b value
    (AspisR1.NFS_QueryInvariant.active p start finish a b d limit inside) canonical)

/-- The executed accumulate of the installed query dictionary is ok at the same states; it is
NFS_AccumInstall.run, whose only raw call is the one of `acc_site`. -/
theorem installed_ok (base : Port3_NativeQueryBody.Ops) {p : verifier.Prepared} {start finish : Nat}
    {a : verifier.Accumulator} {b : verifier.BatchedWeights}
    (d : AspisR1.NFS_QueryInvariant.Domain p start finish a b)
    (limit : finish ≤ 22) (inside : a.next.val < finish) (node : U32) (value : NFP_QueryCuts.E)
    (canonical : NBO_TailDomain.WideCanonical value) :
    AspisR1.Port3_NativeQueryBody.verifier.accumulate_batched_with_node
        (AspisR1.NFS_QueryOps.installed base) p a node value b =
      AspisR1.NFS_AccumInstall.run p a node value b ∧
    ∃ r, AspisR1.NFS_AccumInstall.run p a node value b = ok r := by
  have input := AspisR1.NFS_QueryInvariant.active p start finish a b d limit inside
  obtain ⟨out, h⟩ := acc_site d limit inside node value canonical
  refine ⟨?_, NFS_NEV_TailModel.toPair out, by simp only [AspisR1.NFS_AccumInstall.run, h, bind_tc_ok]⟩
  rw [AspisR1.NFS_QueryOps.accumulation,
    AspisR1.NFS_AccumInstall.installed (AspisR1.NFS_QueryOps.base base) p a node value b input canonical]

#print axioms uadd
#print axioms rows_cut
#print axioms rows_total
#print axioms tail_total
#print axioms acc_total
#print axioms acc_site
#print axioms installed_ok
end AspisR1.NPH_R22Accum
