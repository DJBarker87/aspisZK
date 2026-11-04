import Lean
import NFN_PhaseTransport
import NFS_AccumPart01
import NFS_AccumPart00
import NEI_PushBridge
import NEI_PushRawAssociation
import NBF_Progress
import NFN_GeometryPart05
import NEG_PrefixStep
import KMX_CopyMeaning

-- BEGIN copied NEV_StageWideFields
set_option autoImplicit false
noncomputable section
namespace NFS_NEV_StageWideFields
open Aeneas Aeneas.Std Result AspisR1 NFS_NEV_StageFields

theorem add (x y : E) (hx : NBO_TailDomain.WideCanonical x) (hy : NBO_TailDomain.WideCanonical y) :
    (do let out ← FIo_Native.aspis_core.field.wide_exact.WideExact.add (ne x) (ne y);ok (se out)) =
      NBO_FieldSemantics.add x y := by
  have cx := (canonical_e x).mp hx
  have cy := (canonical_e y).mp hy
  obtain ⟨a,ha,ca,_⟩ := NFS_LPi_TowerValues.qm_add (nq x.c0) (nq y.c0) cx.1 cy.1
  obtain ⟨b,hb,cb,_⟩ := NFS_LPi_TowerValues.qm_add (nq x.c1) (nq y.c1) cx.2 cy.2
  have ma : AspisR1SelectedMaskProbe.field.QM31.add (NBO_FieldPorts.toQ x.c0)
      (NBO_FieldPorts.toQ y.c0)=ok (NFS_NEV_MaskCarriers.toMask a) := by
    have same := NFS_NEV_MaskQM.add (nq x.c0) (nq y.c0) cx.1 cy.1
    exact same.symm.trans (by simp only [ha,bind_tc_ok])
  have mb : AspisR1SelectedMaskProbe.field.QM31.add (NBO_FieldPorts.toQ x.c1)
      (NBO_FieldPorts.toQ y.c1)=ok (NFS_NEV_MaskCarriers.toMask b) := by
    have same := NFS_NEV_MaskQM.add (nq x.c1) (nq y.c1) cx.2 cy.2
    exact same.symm.trans (by simp only [hb,bind_tc_ok])
  simp only [FIo_Native.aspis_core.field.wide_exact.WideExact.add,ne,ha,hb,
    NBO_FieldSemantics.add,ma,mb,bind_tc_ok,NFS_NEV_StageFields.se,NFS_NEV_StageFields.sq,NBO_FieldPorts.fromE,
    NBO_FieldPorts.fromQ,NFS_NEV_MaskCarriers.toMask]

/-- The actual normalization call and both actual component products return
exactly the adopted callback's value, on caller-established canonical inputs. -/
theorem product (x : E) (q : Q) (hx : NBO_TailDomain.WideCanonical x)
    (hq : NBF_PowerStep.Canonical q) :
    (do let out ← FIo_Native.aspis_core.field.wide_exact.WideExact.mul_qm31 (ne x) (nq q);ok (se out)) =
      NBO_FieldSemantics.product x q := by
  have cx := (canonical_e x).mp hx
  have cq := (canonical_q q).mp hq
  have normalized := NFS_NEV_MaskQM.normalization (nq q) cq
  obtain ⟨a,ha,ca,_⟩ := NFS_LPi_TowerValues.qm_mul (nq x.c0) (nq q) cx.1 cq
  obtain ⟨b,hb,cb,_⟩ := NFS_LPi_TowerValues.qm_mul (nq x.c1) (nq q) cx.2 cq
  have ma : AspisR1SelectedMaskProbe.field.QM31.mul (NBO_FieldPorts.toQ x.c0)
      (NBO_FieldPorts.toQ q)=ok (NFS_NEV_MaskCarriers.toMask a) := by
    have same := NFS_NEV_MaskQM.multiply (nq x.c0) (nq q) cx.1 cq
    exact same.symm.trans (by simp only [ha,bind_tc_ok])
  have mb : AspisR1SelectedMaskProbe.field.QM31.mul (NBO_FieldPorts.toQ x.c1)
      (NBO_FieldPorts.toQ q)=ok (NFS_NEV_MaskCarriers.toMask b) := by
    have same := NFS_NEV_MaskQM.multiply (nq x.c1) (nq q) cx.2 cq
    exact same.symm.trans (by simp only [hb,bind_tc_ok])
  simp only [FIo_Native.aspis_core.field.wide_exact.WideExact.mul_qm31,ne,normalized,ha,hb,
    NBO_FieldSemantics.product,ma,mb,bind_tc_ok,NFS_NEV_StageFields.se,NFS_NEV_StageFields.sq,NBO_FieldPorts.fromE,
    NBO_FieldPorts.fromQ,NFS_NEV_MaskCarriers.toMask]
#print axioms add
#print axioms product
end NFS_NEV_StageWideFields
end
-- END copied NEV_StageWideFields
-- BEGIN copied NEV_PrimitiveBindings
set_option autoImplicit false
noncomputable section
namespace NFS_NEV_PrimitiveBindings
open Aeneas Aeneas.Std Result NEV_AccumulateCarriers

theorem power (x y : RawQ) (hx : NBF_PowerStep.Canonical (toQ x))
    (hy : NBF_PowerStep.Canonical (toQ y)) :
    (do let out ← NEV_AccumulateRaw.aspis_core.field.QM31.mul x y;ok (toQ out)) =
      NBO_FieldSemantics.power (toQ x) (toQ y) := by
  unfold NEV_AccumulateRaw.aspis_core.field.QM31.mul
  simp only [bind_assoc_eq,bind_tc_ok]
  exact NFS_NEV_StageFields.power (toQ x) (toQ y) hx hy

theorem add (x y : RawE) (hx : NBO_TailDomain.WideCanonical (toE x))
    (hy : NBO_TailDomain.WideCanonical (toE y)) :
    (do let out ← NEV_AccumulateRaw.aspis_core.field.wide_exact.WideExact.add x y;ok (toE out)) =
      NBO_FieldSemantics.add (toE x) (toE y) := by
  unfold NEV_AccumulateRaw.aspis_core.field.wide_exact.WideExact.add
  simp only [bind_assoc_eq,bind_tc_ok]
  exact NFS_NEV_StageWideFields.add (toE x) (toE y) hx hy

theorem product (x : RawE) (q : RawQ) (hx : NBO_TailDomain.WideCanonical (toE x))
    (hq : NBF_PowerStep.Canonical (toQ q)) :
    (do let out ← NEV_AccumulateRaw.aspis_core.field.wide_exact.WideExact.mul_qm31 x q;ok (toE out)) =
      NBO_FieldSemantics.product (toE x) (toQ q) := by
  unfold NEV_AccumulateRaw.aspis_core.field.wide_exact.WideExact.mul_qm31
  simp only [bind_assoc_eq,bind_tc_ok]
  exact NFS_NEV_StageWideFields.product (toE x) (toQ q) hx hq

/-- The exact field call itself supplies the next call's canonical domain.
A returned product or its successful result is never a premise. -/
theorem product_returns (x : RawE) (q : RawQ) (hx : NBO_TailDomain.WideCanonical (toE x))
    (hq : NBF_PowerStep.Canonical (toQ q)) :
    ∃ out,NEV_AccumulateRaw.aspis_core.field.wide_exact.WideExact.mul_qm31 x q=ok out ∧
      NBO_TailDomain.WideCanonical (toE out) := by
  obtain ⟨model,run,canonical⟩ := NBO_FieldSemantics.product_total (toE x) (toQ q) hx hq
  have same := (product x q hx hq).trans run
  cases actual : NEV_AccumulateRaw.aspis_core.field.wide_exact.WideExact.mul_qm31 x q with
  | fail error => simp only [actual,bind_tc_fail] at same;contradiction
  | div => simp only [actual,bind_tc_div] at same;contradiction
  | ok out =>
    simp only [actual,bind_tc_ok] at same
    have equality := Result.ok.inj same
    refine ⟨out,rfl,?_⟩
    rw [equality]
    exact canonical
#print axioms power
#print axioms add
#print axioms product
#print axioms product_returns
end NFS_NEV_PrimitiveBindings
end
-- END copied NEV_PrimitiveBindings
-- BEGIN copied NEV_PrimitiveTotal
set_option autoImplicit false
noncomputable section
namespace NFS_NEV_PrimitiveTotal
open Aeneas Aeneas.Std Result NEV_AccumulateCarriers

theorem add (x y : RawE) (hx : NBO_TailDomain.WideCanonical (toE x))
    (hy : NBO_TailDomain.WideCanonical (toE y)) :
    ∃ out,NEV_AccumulateRaw.aspis_core.field.wide_exact.WideExact.add x y=ok out ∧
      NBO_TailDomain.WideCanonical (toE out) := by
  obtain ⟨model,run,canonical⟩ := NBO_FieldSemantics.add_total (toE x) (toE y) hx hy
  obtain ⟨out,actual,value⟩ := AspisR1.Port3_PushFrame.bind_success _ _ _
    ((NFS_NEV_PrimitiveBindings.add x y hx hy).trans run)
  refine ⟨out,actual,?_⟩
  rw [Result.ok.inj value]
  exact canonical

theorem power (x y : RawQ) (hx : NBF_PowerStep.Canonical (toQ x))
    (hy : NBF_PowerStep.Canonical (toQ y)) :
    ∃ out,NEV_AccumulateRaw.aspis_core.field.QM31.mul x y=ok out ∧
      NBF_PowerStep.Canonical (toQ out) := by
  obtain ⟨model,run,canonical⟩ := NBO_FieldSemantics.power_total (toQ x) (toQ y) hx hy
  obtain ⟨out,actual,value⟩ := AspisR1.Port3_PushFrame.bind_success _ _ _
    ((NFS_NEV_PrimitiveBindings.power x y hx hy).trans run)
  refine ⟨out,actual,?_⟩
  rw [Result.ok.inj value]
  exact canonical
#print axioms add
#print axioms power
end NFS_NEV_PrimitiveTotal
end
-- END copied NEV_PrimitiveTotal
-- BEGIN copied NEV_TailModel
set_option autoImplicit false
noncomputable section
namespace NFS_NEV_TailModel
open Aeneas Aeneas.Std Result NEV_AccumulateCarriers
open AspisR1 AspisR1Stage2 Port3_NativeQueryBody

def fields (base : Ops) : Ops :=
 {base with op2:=NBO_FieldSemantics.add,op3:=NBO_FieldSemantics.product,op9:=NBO_FieldSemantics.power}
def toPair (pair : NEV_AccumulateRaw.Accumulator × NEV_AccumulateRaw.BatchedWeights) :
    verifier.Accumulator × verifier.BatchedWeights := (toAccumulator pair.1,toWeights pair.2)
def tail (p : verifier.Prepared) (a : verifier.Accumulator) (value : NBF_RowInstall.E)
    (middle : verifier.BatchedWeights) : Result (verifier.Accumulator × verifier.BatchedWeights) := do
 let terms ← middle.terms+1#usize
 let product ← NBO_FieldSemantics.product value a.power
 let rhs ← NBO_FieldSemantics.add a.rhs product
 let power ← NBO_FieldSemantics.power a.power p.rho
 let next ← a.next+1#usize
 ok ({a with rhs:=rhs,power:=power,next:=next},{middle with terms:=terms})

/-- All three intermediate field results and their domains are derived, not
hypotheses. Both checked counter outcomes and full returned carriers remain. -/
theorem association (p : NEV_AccumulateRaw.Prepared) (a : NEV_AccumulateRaw.Accumulator)
    (value : RawE) (middle : NEV_AccumulateRaw.BatchedWeights)
    (hv : NBO_TailDomain.WideCanonical (toE value))
    (hr : NBO_TailDomain.WideCanonical (toE a.rhs))
    (hp : NBF_PowerStep.Canonical (toQ a.power))
    (hq : NBF_PowerStep.Canonical (toQ p.rho)) :
    (do let out ← NFS_NEV_AccumulateTail.tail p a value middle;ok (toPair out)) =
      tail (toPrepared p) (toAccumulator a) (toE value) (toWeights middle) := by
  obtain ⟨product,productRun,productCanonical⟩ := NFS_NEV_PrimitiveBindings.product_returns value a.power hv hp
  obtain ⟨rhs,rhsRun,rhsCanonical⟩ := NFS_NEV_PrimitiveTotal.add a.rhs product hr productCanonical
  obtain ⟨power,powerRun,powerCanonical⟩ := NFS_NEV_PrimitiveTotal.power a.power p.rho hp hq
  have modelProduct : NBO_FieldSemantics.product (toE value) (toQ a.power)=ok (toE product) := by
    simpa only [productRun,bind_tc_ok] using (NFS_NEV_PrimitiveBindings.product value a.power hv hp).symm
  have modelRhs : NBO_FieldSemantics.add (toE a.rhs) (toE product)=ok (toE rhs) := by
    simpa only [rhsRun,bind_tc_ok] using (NFS_NEV_PrimitiveBindings.add a.rhs product hr productCanonical).symm
  have modelPower : NBO_FieldSemantics.power (toQ a.power) (toQ p.rho)=ok (toQ power) := by
    simpa only [powerRun,bind_tc_ok] using (NFS_NEV_PrimitiveBindings.power a.power p.rho hp hq).symm
  simp only [NFS_NEV_AccumulateTail.tail,tail,NEV_AccumulateRaw.trace.value,
    productRun,rhsRun,powerRun,modelProduct,modelRhs,modelPower,bind_assoc_eq,bind_tc_ok,
    toPair,toPrepared,toAccumulator,toWeights]
#print axioms association
end NFS_NEV_TailModel
end
-- END copied NEV_TailModel
-- BEGIN copied NEV_AccumulateComplete
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace NFS_NEV_AccumulateComplete
open Aeneas Aeneas.Std Result NEV_AccumulateCarriers
open AspisR1 AspisR1Stage2 Port3_NativeQueryBody

theorem reference_split (base : Ops) (p : verifier.Prepared) (a : verifier.Accumulator)
    (node : U32) (value : NBF_RowInstall.E) (b : verifier.BatchedWeights) :
    AspisR1Stage2.verifier.accumulateWithOps (NBO_AccumulateAssociation.reference (NFS_NEV_TailModel.fields base))
      p a node value b =
      (do let middle ← NBO_AccumulateAssociation.prefixRun (NFS_NEV_TailModel.fields base) a node b
          NFS_NEV_TailModel.tail p a value middle) := by
  unfold AspisR1Stage2.verifier.accumulateWithOps NBO_AccumulateAssociation.reference
    NBO_AccumulateAssociation.prefixRun NFS_NEV_TailModel.tail
  simp only [NBO_AccumulateAssociation.sourceOps,NBF_Accumulate.install,
    NBF_RowInstall.install,NBF_BasisInstall.install,NFS_NEV_TailModel.fields,bind_assoc_eq,bind_tc_ok]

/-- Complete actual emitted function to the retained adopted accumulation,
with a concrete field dictionary proved in NFS_NEV_PrimitiveBindings. Every full
record field and Result tag is retained. There is no successful-run premise. -/
theorem reference (base : Ops) (p : NEV_AccumulateRaw.Prepared) (a : NEV_AccumulateRaw.Accumulator)
    (node : U32) (value : RawE) (b : NEV_AccumulateRaw.BatchedWeights)
    (width : a.weights.val.length=64) (raw : b.raw.val.length=64) (global : a.next.val<22)
    (hv : NBO_TailDomain.WideCanonical (toE value))
    (hr : NBO_TailDomain.WideCanonical (toE a.rhs))
    (hp : NBF_PowerStep.Canonical (toQ a.power))
    (hq : NBF_PowerStep.Canonical (toQ p.rho)) :
    (do let out ← NEV_AccumulateRaw.accumulate_batched_with_node p a node value b
        ok (NFS_NEV_TailModel.toPair out)) =
      AspisR1Stage2.verifier.accumulateWithOps (NBO_AccumulateAssociation.reference (NFS_NEV_TailModel.fields base))
        (toPrepared p) (toAccumulator a) node (toE value) (toWeights b) := by
  rw [NFS_NEV_AccumulateTail.source_cut,reference_split]
  rw [← NFS_NEV_AccumulatePrefix.association (NFS_NEV_TailModel.fields base) a node b width raw global]
  simp only [bind_assoc_eq,bind_tc_ok]
  have continuations :
      (fun middle : NEV_AccumulateRaw.BatchedWeights =>
        do let out ← NFS_NEV_AccumulateTail.tail p a value middle;ok (NFS_NEV_TailModel.toPair out)) =
      (fun middle : NEV_AccumulateRaw.BatchedWeights =>
        NFS_NEV_TailModel.tail (toPrepared p) (toAccumulator a) (toE value) (toWeights middle)) := by
    funext middle
    exact NFS_NEV_TailModel.association p a value middle hv hr hp hq
  exact congrArg (fun next : NEV_AccumulateRaw.BatchedWeights →
      Result (verifier.Accumulator × verifier.BatchedWeights) =>
    do let middle ← NFS_NEV_AccumulateTail.rows a node b;next middle) continuations

/-- The already-proved NEI independent-counter theorem supplies the exact
native checked/wrapping join, including TX2's distinct local term counter. -/
theorem native (base : Ops) (p : NEV_AccumulateRaw.Prepared) (a : NEV_AccumulateRaw.Accumulator)
    (node : U32) (value : RawE) (b : NEV_AccumulateRaw.BatchedWeights)
    (width : a.weights.val.length=64) (raw : b.raw.val.length=64)
    (global : a.next.val<22) (localActive : b.terms.val<22)
    (hv : NBO_TailDomain.WideCanonical (toE value))
    (hr : NBO_TailDomain.WideCanonical (toE a.rhs))
    (hp : NBF_PowerStep.Canonical (toQ a.power))
    (hq : NBF_PowerStep.Canonical (toQ p.rho)) :
    (do let out ← NEV_AccumulateRaw.accumulate_batched_with_node p a node value b
        ok (NFS_NEV_TailModel.toPair out)) =
      verifier.accumulate_batched_with_node
        (NBO_AccumulateAssociation.sourceOps (NFS_NEV_TailModel.fields base))
        (toPrepared p) (toAccumulator a) node (toE value) (toWeights b) := by
  have mappedWidth : (toAccumulator a).weights.val.length=64 := by
    simpa only [toAccumulator,mapVec,List.length_map] using width
  exact (reference base p a node value b width raw global hv hr hp hq).trans
    (NEI_AccumIndependentCounters.independent_counters (NFS_NEV_TailModel.fields base)
      (toPrepared p) (toAccumulator a) node (toE value) (toWeights b)
      mappedWidth raw global localActive).symm
#print axioms reference_split
#print axioms reference
#print axioms native
end NFS_NEV_AccumulateComplete
end
-- END copied NEV_AccumulateComplete
-- BEGIN copied NEV_PushDomains
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace NFS_NEV_PushDomains
open Aeneas Aeneas.Std Result NEV_AccumulateCarriers AspisR1

def bw (b : NEV_AccumulateRaw.BatchedWeights) : NEI_PushBridge.BW := ⟨b.raw,b.terms⟩
def power (q : RawQ) : NEI_PushBridge.Power :=
 NEI_PushRawAssociation.toPower (NEV_AccumulateRaw.NEV_Bindings.toPushQ q)

theorem canonical_limb (q : RawQ) (canonical : NBF_PowerStep.Canonical (toQ q)) (index : Usize) :
    (S7Kani2OwnedRow.limb (NEG_RowBridge.modelPower (power q)) index).val<2147483647 := by
  have words := (NFS_NEV_StageFields.canonical_q (toQ q)).mp canonical
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
end NFS_NEV_PushDomains
end
-- END copied NEV_PushDomains
-- BEGIN copied NCB_PrefixNativeStep
set_option autoImplicit false
noncomputable section
namespace NFS_NCB_PrefixNativeStep
open Aeneas Aeneas.Std Result ControlFlow AspisR1
open AspisR1.Port4C_NativePrefix S7Kani2PrefixLoop
/-- Three local native cuts compose at ONE arbitrary prefix prestate.
The read, append frame and modular reply are tied to the same flat/index/product.
Ownership and the native whole-loop trace are not assumed or concluded. -/
theorem source (ops : Leaves)
    (multiply : ops.mul=AspisR1Qm31ArithmeticProbe.field.M31.mul)
    (flat : Slice U32) (prefixes after : alloc.vec.Vec U32)
    (product productAfter : U32) (index : Usize)
    (size : flat.val.length≤110) (active : index.val<flat.val.length)
    (capacity : prefixes.val.length≤110)
    (nativePush : after.val=prefixes.val++[product])
    (nativeMul : productAfter.val=(product.val*(flat.val[index.val]'active).val)%2147483647) :
    ∃ next : Usize, next.val=index.val+1 ∧
      verifier.batch_prefix_products_loop.body ops flat prefixes product index=
        ok (cont (after,productAfter,next)) := by
  obtain ⟨x,read,word⟩ := WP.spec_imp_exists (Slice.index_usize_spec flat index active)
  obtain ⟨next,push,contents⟩ := WP.spec_imp_exists
    (alloc.vec.Vec.push_spec prefixes product (by
      have h : 110<Usize.max := by scalar_tac
      omega))
  have same : next=after := Subtype.ext (contents.trans nativePush.symm)
  subst next
  have value : wordMul product x=productAfter := by
    apply UScalar.eq_of_val_eq
    change (product.val*x.val)%2147483647=productAfter.val
    change x=flat.val[index.val] at word
    rw [word]
    exact nativeMul.symm
  let next := Usize.wrapping_add index 1#usize
  refine ⟨next,Port3_Wrapping.increment index (by omega),?_⟩
  have running : index<Slice.len flat := active
  simp only [verifier.batch_prefix_products_loop.body,if_pos running,read,push,
    multiply,multiply_word,value,lift,bind_tc_ok]
  rfl

theorem stopped (ops : Leaves) (flat : Slice U32) (prefixes : alloc.vec.Vec U32)
    (product : U32) (index : Usize) (stop : flat.val.length ≤ index.val) :
    verifier.batch_prefix_products_loop.body ops flat prefixes product index=
      ok (done (prefixes,product)) := by
  have inactive : ¬index<Slice.len flat := by change ¬index.val<flat.val.length;omega
  simp only [verifier.batch_prefix_products_loop.body,if_neg inactive]
#print axioms source
#print axioms stopped
end NFS_NCB_PrefixNativeStep
end
-- END copied NCB_PrefixNativeStep
-- BEGIN copied NCB_PrefixCutTrace
set_option autoImplicit false
noncomputable section
namespace NFS_NCB_PrefixCutTrace
open Aeneas Aeneas.Std Result ControlFlow AspisR1
open AspisR1.Port4C_NativePrefix
/-- Ordered local observations of one actual buffer carrier. Each edge records
only the append frame and modular field reply, not a whole model loop result.
Existence for a frozen native execution remains a separate bridge obligation. -/
inductive Cuts (flat : Slice U32) : Usize → alloc.vec.Vec U32 → U32 →
    alloc.vec.Vec U32 → U32 → Prop
  | done (index : Usize) (buffer : alloc.vec.Vec U32) (product : U32)
      (stop : flat.val.length=index.val) : Cuts flat index buffer product buffer product
  | step (index : Usize) (buffer next final : alloc.vec.Vec U32) (product nextProduct finalProduct : U32)
      (active : index.val<flat.val.length)
      (pushed : next.val=buffer.val++[product])
      (multiplied : nextProduct.val=(product.val*(flat.val[index.val]'active).val)%2147483647)
      (tail : Cuts flat (Usize.wrapping_add index 1#usize) next nextProduct final finalProduct) :
      Cuts flat index buffer product final finalProduct

theorem associated (ops : Leaves)
    (multiply : ops.mul=AspisR1Qm31ArithmeticProbe.field.M31.mul)
    (flat : Slice U32) (size : flat.val.length≤110)
    (index : Usize) (buffer final : alloc.vec.Vec U32) (product finalProduct : U32)
    (cuts : Cuts flat index buffer product final finalProduct)
    (length : buffer.val.length=index.val) :
    verifier.batch_prefix_products_loop ops flat buffer product index=ok (final,finalProduct) := by
  induction cuts with
  | done index buffer product stop =>
    have body := NFS_NCB_PrefixNativeStep.stopped ops flat buffer product index (by omega)
    unfold verifier.batch_prefix_products_loop
    rw [Aeneas.Std.loop.eq_def]
    simp only [Aeneas.Std.uncurry,body]
  | step index buffer next final product nextProduct finalProduct active pushed multiplied tail ih =>
    have inc := Port3_Wrapping.increment index (by omega)
    have nextLen : next.val.length=(Usize.wrapping_add index 1#usize).val := by
      rw [pushed,List.length_append,List.length_singleton,length,inc]
    have tailRun := ih nextLen
    obtain ⟨cursor,cursorVal,body⟩ := NFS_NCB_PrefixNativeStep.source ops multiply flat buffer next
      product nextProduct index size active (by omega) pushed multiplied
    have cursorEq : cursor=Usize.wrapping_add index 1#usize := UScalar.eq_of_val_eq (cursorVal.trans inc.symm)
    rw [cursorEq] at body
    unfold verifier.batch_prefix_products_loop
    rw [Aeneas.Std.loop.eq_def]
    simp only [Aeneas.Std.uncurry,body]
    exact tailRun

/-- Reuse the existing complete buffer meaning theorem after associating the
ordered cuts. This adds no independently chosen native result or product. -/
theorem meaning (ops : Leaves)
    (multiply : ops.mul=AspisR1Qm31ArithmeticProbe.field.M31.mul)
    (one : ops.one=ok (1#u32)) (flat : Slice U32) (size : flat.val.length≤110)
    (final : alloc.vec.Vec U32) (finalProduct : U32)
    (cuts : Cuts flat 0#usize (alloc.vec.Vec.new U32) 1#u32 final finalProduct) :
    (final.val,finalProduct)=S7Kani2PrefixLoop.model flat.val [] 1#u32 := by
  have run := associated ops multiply flat size 0#usize (alloc.vec.Vec.new U32) final
    1#u32 finalProduct cuts rfl
  obtain ⟨out,product,source,value⟩ := Port4C_PrefixMeaning.total ops multiply one flat size
  have entry : verifier.batch_prefix_products ops flat=ok (final,finalProduct) := by
    simp only [verifier.batch_prefix_products,one,bind_tc_ok,alloc.vec.Vec.with_capacity]
    exact run
  have same := Prod.mk.inj (Result.ok.inj (source.symm.trans entry))
  rcases same with ⟨rfl,rfl⟩
  exact value
#print axioms associated
#print axioms meaning
end NFS_NCB_PrefixCutTrace
end
-- END copied NCB_PrefixCutTrace
-- BEGIN copied NEI_PrefixStep
set_option autoImplicit false
noncomputable section
namespace NFS_NEI_PrefixStep
open Aeneas Aeneas.Std Result ControlFlow AspisR1

/-- The same prestate read, appended value, product and index; arbitrary U32 flat. -/
theorem active (flat : Slice U32) (prefixes : alloc.vec.Vec U32)
    (product : U32) (index : Usize) (size : flat.val.length ≤ 110)
    (length : prefixes.val.length = index.val) (running : index.val < flat.val.length) :
    ∃ ps z next, NEG_PrefixFull.batch_prefix_products_loop.body flat prefixes product index =
      ok (cont (ps,z,next)) ∧ ps.val = prefixes.val ++ [product] ∧
      z.val = (product.val * (flat.val[index.val]'running).val) % 2147483647 ∧
      z.val < 2147483647 ∧ next.val = index.val + 1 := by
  obtain ⟨value,read,hvalue⟩ := WP.spec_imp_exists (Slice.index_usize_spec flat index running)
  change value = flat.val[index.val] at hvalue
  have capacity : prefixes.val.length < Usize.max := by
    have roomy : 110 < Usize.max := by scalar_tac
    omega
  obtain ⟨ps,push,pval⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec prefixes product capacity)
  obtain ⟨z,mul,natural,canonical⟩ := NEG_PrefixStep.multiply product value
  have exactProduct : z.val = (product.val * (flat.val[index.val]'running).val) % 2147483647 := by
    simpa only [hvalue] using natural
  obtain ⟨next,nextValue,body⟩ := NFS_NCB_PrefixNativeStep.source NEG_PrefixAssociation.ops rfl
    flat prefixes ps product z index size running (by omega) pval exactProduct
  exact ⟨ps,z,next,(NEG_PrefixAssociation.step flat prefixes product index).trans body,
    pval,exactProduct,canonical,nextValue⟩

theorem stopped (flat : Slice U32) (prefixes : alloc.vec.Vec U32)
    (product : U32) (index : Usize) (done : flat.val.length ≤ index.val) :
    NEG_PrefixFull.batch_prefix_products_loop.body flat prefixes product index =
      ok (ControlFlow.done (prefixes,product)) := by
  exact (NEG_PrefixAssociation.step flat prefixes product index).trans
    (NFS_NCB_PrefixNativeStep.stopped NEG_PrefixAssociation.ops flat prefixes product index done)

/-- Reuse the proved finite induction; no native whole-buffer run is assumed. -/
theorem total (flat : Slice U32) (size : flat.val.length ≤ 110) :
    ∃ ps product, NEG_PrefixFull.batch_prefix_products flat = ok (ps,product) ∧
      (ps.val,product) = S7Kani2PrefixLoop.model flat.val [] 1#u32 := by
  obtain ⟨ps,product,run,meaning⟩ := Port4C_PrefixMeaning.total NEG_PrefixAssociation.ops rfl rfl flat size
  exact ⟨ps,product,(NEG_PrefixAssociation.source flat).trans run,meaning⟩

#print axioms active
#print axioms stopped
#print axioms total
end NFS_NEI_PrefixStep
end
-- END copied NEI_PrefixStep
-- BEGIN copied NEI_PrefixWindows
set_option autoImplicit false
noncomputable section
namespace NFS_NEI_PrefixWindows
open Aeneas Aeneas.Std Result ControlFlow AspisR1

/-- One arbitrary value window plus the length determines the entire append. -/
theorem append_from_windows {T : Type} (before after : List T) (value : T)
    (length : after.length = before.length + 1)
    (windows : ∀ (offset : Nat) (valid : offset < after.length),
      after[offset] = if h : offset < before.length then before[offset] else value) :
    after = before ++ [value] := by
  apply List.ext_getElem
  · simp only [List.length_append,List.length_singleton]
    exact length
  · intro offset ha hb
    rw [windows offset ha]
    by_cases inside : offset < before.length
    · simp only [dif_pos inside,List.getElem_append_left inside]
    · have atEnd : offset = before.length := by omega
      subst offset
      simp

/-- Exact KMX successful-shrink law on an arbitrary surviving location. -/
theorem surviving_copy {T : Type} (src dst : Nat → T) (oldSize newSize offset : Nat)
    (shrinking : newSize ≤ oldSize) (inside : offset < newSize) :
    KMX_CopyMeaning.loop src dst 0 (min oldSize newSize) offset = src offset := by
  rw [KMX_CopyMeaning.realloc_prefix]
  simp only [Nat.min_eq_right shrinking,if_pos inside]

/-- The field operation's actual reply is admitted by the multiplication-free
oracle. The source law supplies its exact value; Kani assumes only the bound. -/
theorem specialize_field_reply (lhs rhs : U32) (P : U32 → Prop)
    (universal : ∀ reply, reply.val < 2147483647 → P reply) :
    ∃ reply, NEG_PrefixFull.aspis_core.field.M31.mul lhs rhs = ok reply ∧
      reply.val = (lhs.val * rhs.val) % 2147483647 ∧ P reply := by
  obtain ⟨reply,run,value,canonical⟩ := NEG_PrefixStep.multiply lhs rhs
  exact ⟨reply,run,value,universal reply canonical⟩

/-- The native local window facts specialize to the SAME emitted source step.
Only primitive append and field-reply observations enter the premises. -/
theorem source_step (flat : Slice U32) (before after : alloc.vec.Vec U32)
    (product reply : U32) (index : Usize) (size : flat.val.length ≤ 110)
    (running : index.val < flat.val.length) (length : before.val.length = index.val)
    (afterLength : after.val.length = before.val.length + 1)
    (windows : ∀ (offset : Nat) (valid : offset < after.val.length),
      after.val[offset] = if h : offset < before.val.length then before.val[offset] else product)
    (fieldReply : reply.val = (product.val * (flat.val[index.val]'running).val) % 2147483647) :
    ∃ next : Usize, next.val = index.val + 1 ∧
      NEG_PrefixFull.batch_prefix_products_loop.body flat before product index =
        ok (cont (after,reply,next)) := by
  have pushed : after.val = before.val ++ [product] :=
    append_from_windows before.val after.val product afterLength windows
  obtain ⟨next,nextValue,body⟩ := NFS_NCB_PrefixNativeStep.source NEG_PrefixAssociation.ops rfl
    flat before after product reply index size running (by omega) pushed fieldReply
  exact ⟨next,nextValue,(NEG_PrefixAssociation.step flat before product index).trans body⟩

#print axioms append_from_windows
#print axioms surviving_copy
#print axioms specialize_field_reply
#print axioms source_step
end NFS_NEI_PrefixWindows
end
-- END copied NEI_PrefixWindows
-- BEGIN copied NEI_PrefixProduct
set_option autoImplicit false
noncomputable section
namespace NFS_NEI_PrefixProduct
open Aeneas Aeneas.Std Result AspisR1

/-- The actual frozen emitted M31 body and prefix's same callee return the
same exact natural value, on every machine-word input. -/
theorem actual (lhs rhs : U32) :
    ∃ reply, NEI_LineFull.aspis_core.field.M31.mul lhs rhs = ok reply ∧
      NEG_PrefixFull.aspis_core.field.M31.mul lhs rhs = ok reply ∧
      reply.val = (lhs.val * rhs.val) % 2147483647 ∧ reply.val < 2147483647 := by
  obtain ⟨reply,run,value,canonical⟩ := NEG_PrefixStep.multiply lhs rhs
  have current : AspisR1CurrentWide.field.M31.mul lhs rhs = ok reply := by
    rw [AspisR1CurrentWide.Proof.m31_mul_same]
    exact run
  exact ⟨reply,(NFS_NEI_FieldScalar.m_mul lhs rhs).trans current,run,value,canonical⟩

/-- Primitive specialization only; no native loop or append result is assumed. -/
theorem specialize (lhs rhs : U32) (P : U32 → Prop)
    (universal : ∀ reply, reply.val < 2147483647 → P reply) :
    ∃ reply, NEI_LineFull.aspis_core.field.M31.mul lhs rhs = ok reply ∧
      NEG_PrefixFull.aspis_core.field.M31.mul lhs rhs = ok reply ∧ P reply := by
  obtain ⟨reply,actualRun,cohortRun,value,canonical⟩ := actual lhs rhs
  exact ⟨reply,actualRun,cohortRun,universal reply canonical⟩

#print axioms actual
#print axioms specialize
end NFS_NEI_PrefixProduct
end
-- END copied NEI_PrefixProduct
-- BEGIN copied NEV_BasisCallDomains
set_option autoImplicit false
noncomputable section
namespace NFS_NEV_BasisCallDomains
open Aeneas Aeneas.Std Result AspisR1
/-- The SAME square result supplies double's canonical domain; the SAME
returned double supplies sub's. Reuse retained scalar total/value laws. -/
theorem scalar (node : U32) : ∃ square doubled out,
    NEV_AccumulateRaw.aspis_core.field.M31.mul node node=ok square ∧ square.val<2147483647 ∧
    NEV_AccumulateRaw.aspis_core.field.M31.double square=ok doubled ∧ doubled.val<2147483647 ∧
    NEV_AccumulateRaw.aspis_core.field.M31.sub doubled 1#u32=ok out ∧ out.val<2147483647 := by
  obtain ⟨square,actual,_,value,canonical⟩ := NFS_NEI_PrefixProduct.actual node node
  obtain ⟨doubled,hd,_,cd⟩ := ExtractedCurrentM31AddSub.current_add_mod square square canonical canonical
  obtain ⟨out,ho,_,co⟩ := ExtractedCurrentM31AddSub.current_sub_mod doubled 1#u32 cd (by decide)
  exact ⟨square,doubled,out,actual,canonical,
    (NFS_NEV_BasisOuterStep.double square).trans hd,cd,
    (NFS_NEV_BasisOuterStep.subtract doubled 1#u32).trans ho,co⟩
/-- Every active width64 level establishes the stricter native window. -/
theorem active_level (n fuel : Nat) (positive : 0<n) (schedule : n*2^(fuel+1)=64) :
    n≤32 ∧ n*2≤64 := by
  have power : 0<2^fuel := by positivity
  have bound := Nat.mul_le_mul_left (n*2) (show 1≤2^fuel by omega)
  rw [pow_succ] at schedule
  constructor <;> nlinarith
#print axioms scalar
#print axioms active_level
end NFS_NEV_BasisCallDomains
end
-- END copied NEV_BasisCallDomains
-- BEGIN copied NEV_WeightDomains
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace NFS_NEV_WeightDomains
open Aeneas Aeneas.Std Result NEV_AccumulateCarriers

def Canonical (v : alloc.vec.Vec RawQ) : Prop := ∀ q∈v.val,NBF_PowerStep.Canonical (toQ q)
/-- SAME actual read establishes the canonical embedding callback domain. -/
theorem read (v : alloc.vec.Vec RawQ) (index : Usize) (inside : index.val<v.val.length)
    (q : RawQ) (run : NEV_AccumulateRaw.accumulated_weight_at v.deref index=ok q)
    (canonical : Canonical v) :
    NFS_NEV_CtorNormalization.Canonical (NEV_AccumulateRaw.NEV_Bindings.toCtorQ q) := by
  obtain ⟨actual,actualRun,point⟩ := WP.spec_imp_exists
    (alloc.vec.Vec.index_usize_spec v index inside)
  have sourceRun : NEV_AccumulateRaw.accumulated_weight_at v.deref index=ok actual := actualRun
  have same : actual=q := Result.ok.inj (sourceRun.symm.trans run)
  have member : q∈v.val := by
    have equality : q=v.val[index.val]'inside := same.symm.trans point
    rw [equality]
    exact List.getElem_mem _
  have values := canonical q member
  exact ⟨⟨values 0,values 1⟩,⟨values 2,values 3⟩⟩
#print axioms read
end NFS_NEV_WeightDomains
end
-- END copied NEV_WeightDomains
-- BEGIN copied NEV_AccumPacket
set_option autoImplicit false
noncomputable section
namespace NFS_NEV_AccumPacket
open Aeneas Aeneas.Std Result NEV_AccumulateCarriers
open AspisR1 AspisR1Stage2 Port3_NativeQueryBody

/-- Input-only packet domain. In particular, no successful child, basis,
row traversal, field result, or complete accumulation result is assumed. -/
structure Domain (p : NEV_AccumulateRaw.Prepared) (a : NEV_AccumulateRaw.Accumulator)
    (value : RawE) (b : NEV_AccumulateRaw.BatchedWeights) : Prop where
 width : a.weights.val.length=64
 weightsCanonical : NFS_NEV_WeightDomains.Canonical a.weights
 global : a.next.val<22
 localActive : b.terms.val<22
 valueCanonical : NBO_TailDomain.WideCanonical (toE value)
 rhsCanonical : NBO_TailDomain.WideCanonical (toE a.rhs)
 powerCanonical : NBF_PowerStep.Canonical (toQ a.power)
 rhoCanonical : NBF_PowerStep.Canonical (toQ p.rho)
 progress : S7JoinRowsTrace.Progress b.terms.val 0 (Port3_RowsInstall.toBW (toWeights b))

theorem raw_length (p : NEV_AccumulateRaw.Prepared) (a : NEV_AccumulateRaw.Accumulator)
    (value : RawE) (b : NEV_AccumulateRaw.BatchedWeights) (domain : Domain p a value b) :
    b.raw.val.length=64 := domain.progress.2.1

/-- Complete modeled Result/state/ordered-effect relation. This ghost state
is external to the returned owned vectors; their actual native mutable frame
is checked separately by the native cut/callee certificates. -/
theorem result_state_effects {S Event : Type} (state : S) (base : Ops)
    (p : NEV_AccumulateRaw.Prepared) (a : NEV_AccumulateRaw.Accumulator)
    (node : U32) (value : RawE) (b : NEV_AccumulateRaw.BatchedWeights)
    (domain : Domain p a value b) :
    (do let out ← NEV_AccumulateRaw.accumulate_batched_with_node p a node value b
        ok (NFS_NEV_TailModel.toPair out,state,([] : List Event))) =
      (do
        let out ← AspisR1Stage2.verifier.accumulateWithOps
            (NBO_AccumulateAssociation.reference (NFS_NEV_TailModel.fields base))
            (toPrepared p) (toAccumulator a) node (toE value) (toWeights b)
        ok (out,state,([] : List Event))) := by
  have same := NFS_NEV_AccumulateComplete.reference base p a node value b domain.width
    (raw_length p a value b domain) domain.global domain.valueCanonical domain.rhsCanonical
    domain.powerCanonical domain.rhoCanonical
  have lifted := congrArg (fun result : Result (verifier.Accumulator × verifier.BatchedWeights) =>
    do let out ← result;ok (out,state,([] : List Event))) same
  simpa only [bind_assoc_eq,bind_tc_ok] using lifted

/-- Any residual base dictionary fields are unreachable by this actual
function. The chosen concrete field/row/basis callbacks determine the result. -/
theorem no_base_dependency (first second : Ops)
    (p : NEV_AccumulateRaw.Prepared) (a : NEV_AccumulateRaw.Accumulator)
    (node : U32) (value : RawE) (b : NEV_AccumulateRaw.BatchedWeights)
    (domain : Domain p a value b) :
    AspisR1Stage2.verifier.accumulateWithOps
      (NBO_AccumulateAssociation.reference (NFS_NEV_TailModel.fields first))
      (toPrepared p) (toAccumulator a) node (toE value) (toWeights b) =
    AspisR1Stage2.verifier.accumulateWithOps
      (NBO_AccumulateAssociation.reference (NFS_NEV_TailModel.fields second))
      (toPrepared p) (toAccumulator a) node (toE value) (toWeights b) := by
  exact (NFS_NEV_AccumulateComplete.reference first p a node value b domain.width
    (raw_length p a value b domain) domain.global domain.valueCanonical domain.rhsCanonical
    domain.powerCanonical domain.rhoCanonical).symm.trans
    (NFS_NEV_AccumulateComplete.reference second p a node value b domain.width
      (raw_length p a value b domain) domain.global domain.valueCanonical domain.rhsCanonical
      domain.powerCanonical domain.rhoCanonical)
#print axioms raw_length
#print axioms result_state_effects
#print axioms no_base_dependency
end NFS_NEV_AccumPacket
end
-- END copied NEV_AccumPacket

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
