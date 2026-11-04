import Lean
import NFN_PhaseTransport
import NFS_AccumPart00
import NBF_BasisInstall
import NBF_BasisOuter
import NBF_BasisDomain
import NBF_Accumulate
import NEI_AccumIndependentCounters
import NFN_GeometryPart02
import AspisR1Post25Sampler.Funs
import ExtractedMaskQM31Mul
import NBO_FieldSemantics

-- BEGIN copied NEI_FieldScalar
set_option autoImplicit false
noncomputable section
namespace NFS_NEI_FieldScalar
open Aeneas Aeneas.Std Result

theorem m_add (x y : U32) :
    NEI_LineFull.aspis_core.field.M31.add x y = AspisR1CurrentWide.field.M31.add x y := by
  simp only [NEI_LineFull.aspis_core.field.M31.add, AspisR1CurrentWide.field.M31.add,
    NEI_LineFull.aspis_core.field.P, AspisR1CurrentWide.field.P]

theorem m_sub (x y : U32) :
    NEI_LineFull.aspis_core.field.M31.sub x y = AspisR1CurrentWide.field.M31.sub x y := by
  simp only [NEI_LineFull.aspis_core.field.M31.sub, AspisR1CurrentWide.field.M31.sub,
    NEI_LineFull.aspis_core.field.P, AspisR1CurrentWide.field.P]

theorem reduce (x : U64) : NEI_LineFull.aspis_core.field.reduce_u64 x =
    AspisR1CurrentWide.field.reduce_u64 x := by
  simp only [NEI_LineFull.aspis_core.field.reduce_u64, AspisR1CurrentWide.field.reduce_u64,
    NEI_LineFull.aspis_core.field.P, AspisR1CurrentWide.field.P]

theorem m_reduce_u64 (x : U64) : NEI_LineFull.aspis_core.field.M31.reduce_u64 x =
    AspisR1CurrentWide.field.M31.reduce_u64 x := by
  simp only [NEI_LineFull.aspis_core.field.M31.reduce_u64,
    AspisR1CurrentWide.field.M31.reduce_u64, reduce]

theorem m_mul (x y : U32) : NEI_LineFull.aspis_core.field.M31.mul x y =
    AspisR1CurrentWide.field.M31.mul x y := by
  simp only [NEI_LineFull.aspis_core.field.M31.mul, AspisR1CurrentWide.field.M31.mul,reduce]

theorem m_double (x : U32) : NEI_LineFull.aspis_core.field.M31.double x =
    AspisR1CurrentWide.field.M31.double x := by
  simp only [NEI_LineFull.aspis_core.field.M31.double, AspisR1CurrentWide.field.M31.double,m_add]

#print axioms m_add
#print axioms m_sub
#print axioms reduce
#print axioms m_reduce_u64
#print axioms m_mul
#print axioms m_double
end NFS_NEI_FieldScalar
end
-- END copied NEI_FieldScalar
-- BEGIN copied NEV_BasisRaw
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace NFS_NEV_BasisRaw
open Aeneas Aeneas.Std Result ControlFlow
open AspisR1 AspisR1Stage2 Port3_NativeQueryBody
/-- New actual-body association only. Arithmetic is the imported closed field
bridge, and the recurrence/induction below is the retained NBF/S7 recurrence. -/
theorem inner_step (ops : Ops) (node : U32) (n : Usize)
    (iter : core.ops.range.Range Usize) (basis : Array U32 256#usize)
    (small : n.val≤128) (finish : iter.end=n) (active : iter.start.val<n.val) :
    NEV_AccumulateRaw.accumulate_batched_with_node_loop0_loop0.body node n iter basis =
      verifier.accumulate_batched_with_node_loop0_loop0.body
        (NBF_BasisInstall.install ops) node n iter basis := by
  obtain ⟨⟨o,iter1⟩,run,ho,hs,he⟩ := WP.spec_imp_exists
    (core.iter.range.IteratorRange.next_UScalar_some_spec
      (ty:=.Usize) (cloneInst:=core.clone.CloneUsize)
      (partialOrdInst:=core.cmp.PartialOrdUsize) (by intro x;rfl) (by intro x y;rfl)
      iter (by rw [finish];exact active))
  subst o
  have add := Port3_Wrapping.checked_add n iter.start (by omega)
  simp [NEV_AccumulateRaw.accumulate_batched_with_node_loop0_loop0.body,
    verifier.accumulate_batched_with_node_loop0_loop0.body,run,bind_tc_ok,
    NEV_AccumulateRaw.aspis_core.field.M31.mul,NFS_NEI_FieldScalar.m_mul,
    AspisR1CurrentWide.Proof.m31_mul_same,NBF_BasisInstall.install,add,lift]

theorem inner_stop (ops : Ops) (node : U32) (n : Usize)
    (iter : core.ops.range.Range Usize) (basis : Array U32 256#usize)
    (done : iter.end.val≤ iter.start.val) :
    NEV_AccumulateRaw.accumulate_batched_with_node_loop0_loop0.body node n iter basis =
      verifier.accumulate_batched_with_node_loop0_loop0.body
        (NBF_BasisInstall.install ops) node n iter basis := by
  obtain ⟨⟨o,iter1⟩,run,ho,hi⟩ := WP.spec_imp_exists
    (core.iter.range.IteratorRange.next_UScalar_none_spec
      (ty:=.Usize) (cloneInst:=core.clone.CloneUsize)
      (partialOrdInst:=core.cmp.PartialOrdUsize) (by intro x y;rfl) iter done)
  subst o
  simp only [NEV_AccumulateRaw.accumulate_batched_with_node_loop0_loop0.body,
    verifier.accumulate_batched_with_node_loop0_loop0.body,run,bind_tc_ok]
  rfl

/-- The only new induction transports the newly imported checked Rust loop to
its already-proved NBF emitted loop. No basis arithmetic is reproved. -/
theorem inner_loop (ops : Ops) (node : U32) (n : Usize) (fuel : Nat)
    (iter : core.ops.range.Range Usize) (basis : Array U32 256#usize)
    (small : n.val≤128) (finish : iter.end=n) (span : iter.start.val+fuel=n.val) :
    NEV_AccumulateRaw.accumulate_batched_with_node_loop0_loop0 iter node basis n =
      verifier.accumulate_batched_with_node_loop0_loop0 (NBF_BasisInstall.install ops)
        iter node basis n := by
  induction fuel generalizing iter basis with
  | zero =>
    unfold NEV_AccumulateRaw.accumulate_batched_with_node_loop0_loop0
      verifier.accumulate_batched_with_node_loop0_loop0
    rw [Aeneas.Std.loop.eq_def,Aeneas.Std.loop.eq_def]
    dsimp only
    have done : iter.end.val≤ iter.start.val := by rw [finish];omega
    rw [inner_stop ops node n iter basis done]
    rw [NBF_Basis.stop (NBF_BasisInstall.install ops) node n iter basis done]
  | succ k ih =>
    have active : iter.start.val<n.val := by omega
    obtain ⟨iter1,hs,he,body⟩ := NBF_Basis.step (NBF_BasisInstall.install ops)
      node n iter basis small finish active
    unfold NEV_AccumulateRaw.accumulate_batched_with_node_loop0_loop0
      verifier.accumulate_batched_with_node_loop0_loop0
    rw [Aeneas.Std.loop.eq_def,Aeneas.Std.loop.eq_def]
    dsimp only
    rw [inner_step ops node n iter basis small finish active,body]
    cases step : S7Kani2BasisLoop.step (NBF_BasisInstall.install ops).op7 node n iter.start basis with
    | fail e => simp only [step,bind_tc_fail]
    | div => simp only [step,bind_tc_div]
    | ok out =>
      simp only [step,bind_tc_ok]
      exact ih iter1 out (he.trans finish) (by omega)

#print axioms inner_step
#print axioms inner_stop
#print axioms inner_loop
end NFS_NEV_BasisRaw
end
-- END copied NEV_BasisRaw
-- BEGIN copied NEV_BasisOuterStep
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace NFS_NEV_BasisOuterStep
open Aeneas Aeneas.Std Result ControlFlow AspisR1 AspisR1Stage2 Port3_NativeQueryBody

theorem multiply (x y : U32) : NEV_AccumulateRaw.aspis_core.field.M31.mul x y=
    AspisR1Qm31ArithmeticProbe.field.M31.mul x y := by
  rw [NEV_AccumulateRaw.aspis_core.field.M31.mul,NFS_NEI_FieldScalar.m_mul,
    AspisR1CurrentWide.Proof.m31_mul_same]
theorem subtract (x y : U32) : NEV_AccumulateRaw.aspis_core.field.M31.sub x y=
    AspisR1Qm31ArithmeticProbe.field.M31.sub x y := by
  rw [NEV_AccumulateRaw.aspis_core.field.M31.sub,NFS_NEI_FieldScalar.m_sub,
    AspisR1CurrentWide.Proof.m31_sub_same]
theorem double (x : U32) : NEV_AccumulateRaw.aspis_core.field.M31.double x=
    AspisR1Qm31ArithmeticProbe.field.M31.add x x := by
  change NEI_LineFull.aspis_core.field.M31.add x x=_
  rw [NFS_NEI_FieldScalar.m_add,AspisR1CurrentWide.Proof.m31_add_same]

/-- New emitted outer body uses the SAME retained inner loop, same node update,
and nonwrapping bounded doubling. No arithmetic recurrence is reproved. -/
theorem body (ops : Ops) (one node : U32) (width n : Usize)
    (basis : Array U32 256#usize) (small : n.val≤128) :
    NEV_AccumulateRaw.accumulate_batched_with_node_loop0.body one width node basis n =
      verifier.accumulate_batched_with_node_loop0.body
        (NBF_BasisInstall.install ops) one width node basis n := by
  have inner := NFS_NEV_BasisRaw.inner_loop ops node n n.val
    {start:=0#usize,«end»:=n} basis small rfl (by simp)
  have counter := NBF_BasisInstall.checked_mul n 2#usize (by change n.val*2≤4096;omega)
  simp [NEV_AccumulateRaw.accumulate_batched_with_node_loop0.body,
    verifier.accumulate_batched_with_node_loop0.body,inner,NBF_BasisInstall.install,
    multiply,subtract,double,counter,lift]

#print axioms multiply
#print axioms subtract
#print axioms double
#print axioms body
end NFS_NEV_BasisOuterStep
end
-- END copied NEV_BasisOuterStep
-- BEGIN copied NEV_BasisOuterRaw
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace NFS_NEV_BasisOuterRaw
open Aeneas Aeneas.Std Result ControlFlow AspisR1 AspisR1Stage2 Port3_NativeQueryBody
open S7Kani3BasisOuter (levels t2 double)
/-- Transport the new emitted outer loop through the retained six-level
schedule. Existing S7 totality supplies intermediate basis/node results. -/
theorem levels_eq (ops : Ops) (fuel : Nat) (basis : Array U32 256#usize)
    (node : U32) (n width : Usize) (positive : 0<n.val) (bound : width.val≤256)
    (schedule : n.val*2^fuel=width.val) :
    NEV_AccumulateRaw.accumulate_batched_with_node_loop0 1#u32 node width basis n=
      verifier.accumulate_batched_with_node_loop0 (NBF_BasisInstall.install ops)
        1#u32 node width basis n := by
  induction fuel generalizing basis node n with
  | zero =>
    have done : ¬n<width := by
      change ¬n.val<width.val
      simp only [pow_zero,Nat.mul_one] at schedule
      omega
    unfold NEV_AccumulateRaw.accumulate_batched_with_node_loop0
      verifier.accumulate_batched_with_node_loop0
    rw [Aeneas.Std.loop.eq_def,Aeneas.Std.loop.eq_def]
    dsimp only
    simp only [NEV_AccumulateRaw.accumulate_batched_with_node_loop0.body,
      verifier.accumulate_batched_with_node_loop0.body,if_neg done,bind_tc_ok]
  | succ k ih =>
    have power : 0<2^k := by positivity
    have doubleBound : n.val*2≤width.val := by
      have : 1≤2^k := by omega
      have := Nat.mul_le_mul_left (n.val*2) this
      rw [pow_succ] at schedule
      nlinarith
    have small : n.val≤128 := by omega
    have active : n<width := by
      change n.val<width.val
      have : 2≤2^(k+1) := by rw [pow_succ];omega
      nlinarith
    let n1 := Usize.wrapping_mul n 2#usize
    have successor : n1.val=n.val*2 := Port3_Wrapping.wrap_mul_value n 2#usize
      (by change n.val*2≤4096;omega)
    have block := NBF_BasisInstall.block ops basis node n small
    have body : verifier.accumulate_batched_with_node_loop0.body
        (NBF_BasisInstall.install ops) 1#u32 width node basis n=
        (do let b1 ← S7Kani2BasisLoop.basis_block_owned
              AspisR1Qm31ArithmeticProbe.field.M31.mul basis node n 0#usize
            let node1 ← t2 node
            ok (cont (node1,b1,n1))) := by
      unfold verifier.accumulate_batched_with_node_loop0.body
      rw [if_pos active,block]
      simp only [NBF_BasisInstall.install,t2,double,lift,bind_tc_ok,bind_assoc_eq]
      rfl
    unfold NEV_AccumulateRaw.accumulate_batched_with_node_loop0
      verifier.accumulate_batched_with_node_loop0
    rw [Aeneas.Std.loop.eq_def,Aeneas.Std.loop.eq_def]
    dsimp only
    rw [NFS_NEV_BasisOuterStep.body ops 1#u32 node width n basis small,body]
    obtain ⟨b1,hb⟩ := S7Kani3BasisTotal.block_total basis node n 0#usize n.val small (by simp)
    obtain ⟨node1,ht,hcanon⟩ := S7Kani3BasisOuter.t2_total node
    simp only [hb,ht,bind_tc_ok]
    exact ih b1 node1 n1 (by rw [successor];omega) (by
      rw [successor]
      rw [pow_succ] at schedule
      nlinarith)

#print axioms levels_eq
end NFS_NEV_BasisOuterRaw
end
-- END copied NEV_BasisOuterRaw
-- BEGIN copied NEV_BasisProducer
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace NFS_NEV_BasisProducer
open Aeneas Aeneas.Std Result

def source (node : U32) : Result (Array U32 256#usize) := do
 let initial ← Array.update (Array.repeat 256#usize 0#u32) 0#usize 1#u32
 NEV_AccumulateRaw.accumulate_batched_with_node_loop0 1#u32 node 64#usize initial 1#usize
/-- The actual width64 initialization and six-level loop reach exactly the
retained basis producer, for every raw input node. -/
theorem association (ops : AspisR1.Port3_NativeQueryBody.Ops) (node : U32) :
    source node=NBF_BasisDomain.source ops node := by
  have continuations :
      (fun initial : Array U32 256#usize =>
        NEV_AccumulateRaw.accumulate_batched_with_node_loop0 1#u32 node 64#usize initial 1#usize) =
      (fun initial : Array U32 256#usize =>
        AspisR1.Port3_NativeQueryBody.verifier.accumulate_batched_with_node_loop0
          (NBF_BasisInstall.install ops) 1#u32 node 64#usize initial 1#usize) := by
    funext initial
    exact NFS_NEV_BasisOuterRaw.levels_eq ops 6 initial node 1#usize 64#usize
      (by decide) (by decide) (by decide)
  exact congrArg (fun next : Array U32 256#usize → Result (Array U32 256#usize) =>
    do let initial ← Array.update (Array.repeat 256#usize 0#u32) 0#usize 1#u32
       next initial) continuations

theorem total (ops : AspisR1.Port3_NativeQueryBody.Ops) (node : U32) :
    ∃ basis,source node=ok basis ∧ AspisR1.S7JoinBasisCanonical.Canonical basis := by
  rw [association ops node]
  exact NBF_BasisDomain.total ops node
/-- Caller domain is derived from the SAME actual returned basis and read. -/
theorem read_canonical (ops : AspisR1.Port3_NativeQueryBody.Ops) (node : U32)
    (basis : Array U32 256#usize) (run : source node=ok basis)
    (index : Usize) (inside : index.val<256) (word : U32)
    (read : NEV_AccumulateRaw.basis_at basis index=ok word) : word.val<2147483647 := by
  rw [association ops node] at run
  exact NBF_BasisDomain.read_canonical ops node basis run index inside word read
#print axioms association
#print axioms total
#print axioms read_canonical
end NFS_NEV_BasisProducer
end
-- END copied NEV_BasisProducer
-- BEGIN copied NEV_AccumulateTail
set_option autoImplicit false
noncomputable section
namespace NFS_NEV_AccumulateTail
open Aeneas Aeneas.Std Result NEV_AccumulateRaw
/-- Exact newly emitted prefix, not a successful-loop assumption. -/
def rows (a : Accumulator) (node : U32) (weights : BatchedWeights) : Result BatchedWeights := do
 let width := alloc.vec.Vec.len a.weights
 let zero ← aspis_core.field.M31.ZERO
 let one ← aspis_core.field.M31.ONE
 let initialized ← Array.update (Array.repeat 256#usize zero) 0#usize one
 let basis ← accumulate_batched_with_node_loop0 one node width initialized 1#usize
 accumulate_batched_with_node_loop1 {start:=0#usize,«end»:=width}
   a.weights a.power a.next weights width basis
/-- Exact checked counter updates and concrete lower field callees. -/
def tail (p : Prepared) (a : Accumulator)
    (value : aspis_core.field.wide_exact.WideExact) (weights : BatchedWeights) :
    Result (Accumulator × BatchedWeights) := do
 let terms ← weights.terms+1#usize
 let product ← aspis_core.field.wide_exact.WideExact.mul_qm31 value a.power
 let rhs ← aspis_core.field.wide_exact.WideExact.add a.rhs product
 trace.value 11#u16 a.next rhs
 let power ← aspis_core.field.QM31.mul a.power p.rho
 let next ← a.next+1#usize
 ok ({a with rhs:=rhs,power:=power,next:=next},{weights with terms:=terms})

/-- Full Result decomposition: failed/divergent prefix or field call is kept,
including the original order of both independent counter operations. -/
theorem source_cut (p : Prepared) (a : Accumulator) (node : U32)
    (value : aspis_core.field.wide_exact.WideExact) (weights : BatchedWeights) :
    accumulate_batched_with_node p a node value weights =
      (do let middle ← rows a node weights;tail p a value middle) := by
  unfold accumulate_batched_with_node rows tail
  simp only [bind_assoc_eq,bind_tc_ok]

/-- The tail returns exactly the SAME vectors. This is a model carrier frame;
the native mutable/physical frame is separately checked by K036/K037. -/
theorem successful_frame (p : Prepared) (a out : Accumulator)
    (value : aspis_core.field.wide_exact.WideExact) (middle result : BatchedWeights)
    (run : tail p a value middle=ok (out,result)) :
    out.weights=a.weights ∧ result.raw=middle.raw := by
  unfold tail at run
  iterate 6 obtain ⟨x,hx,run⟩ := AspisR1.Port3_PushFrame.bind_success _ _ _ run
  cases Result.ok.inj run
  exact ⟨rfl,rfl⟩

#print axioms source_cut
#print axioms successful_frame
end NFS_NEV_AccumulateTail
end
-- END copied NEV_AccumulateTail
-- BEGIN copied NEV_AccumulatePrefix
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace NFS_NEV_AccumulatePrefix
open Aeneas Aeneas.Std Result NEV_AccumulateCarriers
open AspisR1 AspisR1Stage2 Port3_NativeQueryBody

theorem installs_commute (ops : Ops) :
    NBF_BasisInstall.install (NBF_RowInstall.install ops)=NBF_Accumulate.install ops := rfl

/-- Exact prefix including initialization, six-level basis production and all
64 rows. No successful prefix output is supplied as a hypothesis. -/
theorem association (ops : Ops) (a : NEV_AccumulateRaw.Accumulator) (node : U32)
    (b : NEV_AccumulateRaw.BatchedWeights) (width : a.weights.val.length=64)
    (raw : b.raw.val.length=64) (global : a.next.val<22) :
    (do let out ← NFS_NEV_AccumulateTail.rows a node b;ok (toWeights out)) =
      NBO_AccumulateAssociation.prefixRun ops (toAccumulator a) node (toWeights b) := by
  have rawWidth : alloc.vec.Vec.len a.weights=64#usize := UScalar.eq_of_val_eq width
  have modelWidth : alloc.vec.Vec.len (toAccumulator a).weights=64#usize := by
    apply UScalar.eq_of_val_eq
    change (mapVec toQ a.weights).val.length=64
    simpa only [mapVec,List.length_map] using width
  have source : NFS_NEV_AccumulateTail.rows a node b=
      (do let basis ← NFS_NEV_BasisProducer.source node
          NEV_AccumulateRaw.accumulate_batched_with_node_loop1
            {start:=0#usize,«end»:=64#usize} a.weights a.power a.next b 64#usize basis) := by
    unfold NFS_NEV_AccumulateTail.rows NFS_NEV_BasisProducer.source
    rw [rawWidth]
    simp only [NEV_AccumulateRaw.aspis_core.field.M31.ZERO,
      NEV_AccumulateRaw.aspis_core.field.M31.ONE,bind_tc_ok,bind_assoc_eq]
  have target : NBO_AccumulateAssociation.prefixRun ops (toAccumulator a) node (toWeights b)=
      (do let basis ← NBF_BasisDomain.source (NBF_RowInstall.install ops) node
          verifier.accumulate_batched_with_node_loop1 (NBF_Accumulate.install ops)
            {start:=0#usize,«end»:=64#usize} (mapVec toQ a.weights) (toQ a.power)
            a.next (toWeights b) 64#usize basis) := by
    unfold NBO_AccumulateAssociation.prefixRun NBF_BasisDomain.source
    rw [modelWidth]
    rw [installs_commute]
    rfl
  rw [source,target]
  simp only [bind_assoc_eq]
  rw [NFS_NEV_BasisProducer.association (NBF_RowInstall.install ops) node]
  have continuation :
      (fun basis : Array U32 256#usize =>
        do let out ← NEV_AccumulateRaw.accumulate_batched_with_node_loop1
             {start:=0#usize,«end»:=64#usize} a.weights a.power a.next b 64#usize basis
           ok (toWeights out)) =
      (fun basis : Array U32 256#usize =>
        verifier.accumulate_batched_with_node_loop1 (NBF_Accumulate.install ops)
          {start:=0#usize,«end»:=64#usize} (mapVec toQ a.weights) (toQ a.power)
          a.next (toWeights b) 64#usize basis) := by
    funext basis
    exact NFS_NEV_RowLoop.association (NBF_BasisInstall.install ops)
      a.weights a.power a.next basis 64 {start:=0#usize,«end»:=64#usize} b
      width raw rfl rfl global
  exact congrArg (fun continuation : Array U32 256#usize → Result AspisR1Stage2.verifier.BatchedWeights =>
    do let basis ← NBF_BasisDomain.source (NBF_RowInstall.install ops) node
       continuation basis) continuation
#print axioms installs_commute
#print axioms association
end NFS_NEV_AccumulatePrefix
end
-- END copied NEV_AccumulatePrefix
-- BEGIN copied LPi_TowerValues
set_option autoImplicit false
namespace AspisR1.NFS_LPi_TowerValues
open Aeneas Aeneas.Std Result NFN_LPi_FieldValues

theorem qm_add (x y : NQ) (hx : canonQ x) (hy : canonQ y) :
    ∃ z, FIo_Native.aspis_core.field.QM31.add x y = ok z ∧ canonQ z ∧
      qw z = addQ (qw x) (qw y) := by
  obtain ⟨a,ha,ca,va⟩ := cm_add x.c0 y.c0 hx.1 hy.1
  obtain ⟨b,hb,cb,vb⟩ := cm_add x.c1 y.c1 hx.2 hy.2
  refine ⟨⟨a,b⟩,?_,⟨ca,cb⟩,Prod.ext va vb⟩
  simp only [FIo_Native.aspis_core.field.QM31.add,ha,hb,bind_tc_ok]

theorem qm_sub (x y : NQ) (hx : canonQ x) (hy : canonQ y) :
    ∃ z, FIo_Native.aspis_core.field.QM31.sub x y = ok z ∧ canonQ z ∧
      qw z = subQ (qw x) (qw y) := by
  obtain ⟨a,ha,ca,va⟩ := cm_sub x.c0 y.c0 hx.1 hy.1
  obtain ⟨b,hb,cb,vb⟩ := cm_sub x.c1 y.c1 hx.2 hy.2
  refine ⟨⟨a,b⟩,?_,⟨ca,cb⟩,Prod.ext va vb⟩
  simp only [FIo_Native.aspis_core.field.QM31.sub,ha,hb,bind_tc_ok]

theorem qm_mul (x y : NQ) (hx : canonQ x) (hy : canonQ y) :
    ∃ z, FIo_Native.aspis_core.field.QM31.mul x y = ok z ∧ canonQ z ∧
      qw z = mulQ (qw x) (qw y) := by
  obtain ⟨ac,hac,cac,vac⟩ := cm_mul x.c0 y.c0 hx.1 hy.1
  obtain ⟨bd,hbd,cbd,vbd⟩ := cm_mul x.c1 y.c1 hx.2 hy.2
  obtain ⟨a,ha,ca,va⟩ := cm_add x.c0 x.c1 hx.1 hx.2
  obtain ⟨b,hb,cb,vb⟩ := cm_add y.c0 y.c1 hy.1 hy.2
  obtain ⟨cross,hcross,ccross,vcross⟩ := cm_mul a b ca cb
  obtain ⟨r,hr,cr,vr⟩ := by_r bd cbd
  obtain ⟨lo,hlo,clo,vlo⟩ := cm_add ac r cac cr
  obtain ⟨diff,hdiff,cdiff,vdiff⟩ := cm_sub cross ac ccross cac
  obtain ⟨hi,hhi,chi,vhi⟩ := cm_sub diff bd cdiff cbd
  refine ⟨⟨lo,hi⟩,?_,⟨clo,chi⟩,?_⟩
  · simp only [FIo_Native.aspis_core.field.QM31.mul,hac,hbd,ha,hb,hcross,hr,hlo,hdiff,hhi,bind_tc_ok]
  · simp only [qw,mulQ]
    rw [vlo,vhi,vdiff,vr,vcross,va,vb,vac,vbd]


theorem mul_u (x : NQ) (hx : canonQ x) :
    ∃ z, FIo_Native.aspis_core.field.wide_exact.mul_u x = ok z ∧ canonQ z ∧
      qw z = mulU (qw x) := by
  obtain ⟨a,ha,ca,va⟩ := by_r x.c1 hx.2
  refine ⟨⟨a,x.c0⟩,?_,⟨ca,hx.1⟩,Prod.ext va rfl⟩
  simp only [FIo_Native.aspis_core.field.wide_exact.mul_u,ha,bind_tc_ok]

theorem wide_mul (x y : NE) (hx : canonE x) (hy : canonE y) :
    ∃ z, FIo_Native.aspis_core.field.wide_exact.WideExact.mul x y = ok z ∧ canonE z ∧
      ew z = mulE (ew x) (ew y) := by
  obtain ⟨ac,hac,cac,vac⟩ := qm_mul x.c0 y.c0 hx.1 hy.1
  obtain ⟨bd,hbd,cbd,vbd⟩ := qm_mul x.c1 y.c1 hx.2 hy.2
  obtain ⟨a,ha,ca,va⟩ := qm_add x.c0 x.c1 hx.1 hx.2
  obtain ⟨b,hb,cb,vb⟩ := qm_add y.c0 y.c1 hy.1 hy.2
  obtain ⟨cross,hcross,ccross,vcross⟩ := qm_mul a b ca cb
  obtain ⟨r,hr,cr,vr⟩ := mul_u bd cbd
  obtain ⟨lo,hlo,clo,vlo⟩ := qm_add ac r cac cr
  obtain ⟨diff,hdiff,cdiff,vdiff⟩ := qm_sub cross ac ccross cac
  obtain ⟨hi,hhi,chi,vhi⟩ := qm_sub diff bd cdiff cbd
  refine ⟨⟨lo,hi⟩,?_,⟨clo,chi⟩,?_⟩
  · simp only [FIo_Native.aspis_core.field.wide_exact.WideExact.mul,hac,hbd,ha,hb,hcross,hr,hlo,hdiff,hhi,bind_tc_ok]
  · simp only [ew,mulE]
    rw [vlo,vhi,vdiff,vr,vcross,va,vb,vac,vbd]

#print axioms qm_add
#print axioms qm_sub
#print axioms qm_mul
#print axioms mul_u
#print axioms wide_mul
end AspisR1.NFS_LPi_TowerValues
-- END copied LPi_TowerValues
-- BEGIN copied LPi_MixedValues
set_option autoImplicit false
namespace AspisR1.NFS_LPi_MixedValues
open Aeneas Aeneas.Std Result NFN_LPi_FieldValues

theorem cm_m31 (x : NC) (s : U32) : ∃ z,
    FIo_Native.aspis_core.field.CM31.mul_m31 x s = ok z ∧ canonC z ∧
      cw z = ((x.a.val*s.val)%2147483647,(x.b.val*s.val)%2147483647) := by
  obtain ⟨a,ha,va,ca⟩ := NFN_LPf_BaseMultiply.source x.a s
  obtain ⟨b,hb,vb,cb⟩ := NFN_LPf_BaseMultiply.source x.b s
  exact ⟨⟨a,b⟩,by simp only [FIo_Native.aspis_core.field.CM31.mul_m31,ha,hb,bind_tc_ok],
    ⟨ca,cb⟩,Prod.ext va vb⟩

theorem qm_m31 (x : NQ) (s : U32) : ∃ z,
    FIo_Native.aspis_core.field.QM31.mul_m31 x s = ok z ∧ canonQ z ∧
      qw z = (((x.c0.a.val*s.val)%2147483647,(x.c0.b.val*s.val)%2147483647),
        ((x.c1.a.val*s.val)%2147483647,(x.c1.b.val*s.val)%2147483647)) := by
  obtain ⟨a,ha,ca,va⟩ := cm_m31 x.c0 s
  obtain ⟨b,hb,cb,vb⟩ := cm_m31 x.c1 s
  exact ⟨⟨a,b⟩,by simp only [FIo_Native.aspis_core.field.QM31.mul_m31,ha,hb,bind_tc_ok],
    ⟨ca,cb⟩,Prod.ext va vb⟩

#print axioms cm_m31
#print axioms qm_m31
end AspisR1.NFS_LPi_MixedValues
-- END copied LPi_MixedValues
-- BEGIN copied LPf_WideConstruction
set_option autoImplicit false
namespace AspisR1.NFS_LPf_WideConstruction
open Aeneas Aeneas.Std Result
abbrev E := FIo_Native.aspis_core.field.wide_exact.WideExact

def value (a b c d e f g h : U32) : E :=
  ⟨⟨⟨a,b⟩,⟨c,d⟩⟩,⟨⟨e,f⟩,⟨g,h⟩⟩⟩

theorem source (a b c d e f g h : U32)
    (ha : a.val < 2147483647) (hb : b.val < 2147483647)
    (hc : c.val < 2147483647) (hd : d.val < 2147483647)
    (he : e.val < 2147483647) (hf : f.val < 2147483647)
    (hg : g.val < 2147483647) (hh : h.val < 2147483647) :
    FIo_Native.aspis_core.field.wide_exact.WideExact.from_limbs
      (Array.make 8#usize [a,b,c,d,e,f,g,h]) = ok (some (value a b c d e f g h)) := by
  have i0 : Array.index_usize (Array.make 8#usize [a,b,c,d,e,f,g,h]) 0#usize = ok a := rfl
  have i1 : Array.index_usize (Array.make 8#usize [a,b,c,d,e,f,g,h]) 1#usize = ok b := rfl
  have i2 : Array.index_usize (Array.make 8#usize [a,b,c,d,e,f,g,h]) 2#usize = ok c := rfl
  have i3 : Array.index_usize (Array.make 8#usize [a,b,c,d,e,f,g,h]) 3#usize = ok d := rfl
  have i4 : Array.index_usize (Array.make 8#usize [a,b,c,d,e,f,g,h]) 4#usize = ok e := rfl
  have i5 : Array.index_usize (Array.make 8#usize [a,b,c,d,e,f,g,h]) 5#usize = ok f := rfl
  have i6 : Array.index_usize (Array.make 8#usize [a,b,c,d,e,f,g,h]) 6#usize = ok g := rfl
  have i7 : Array.index_usize (Array.make 8#usize [a,b,c,d,e,f,g,h]) 7#usize = ok h := rfl
  have na : ¬a ≥ 2147483647#u32 := by scalar_tac
  have nb : ¬b ≥ 2147483647#u32 := by scalar_tac
  have nc : ¬c ≥ 2147483647#u32 := by scalar_tac
  have nd : ¬d ≥ 2147483647#u32 := by scalar_tac
  have ne : ¬e ≥ 2147483647#u32 := by scalar_tac
  have nf : ¬f ≥ 2147483647#u32 := by scalar_tac
  have ng : ¬g ≥ 2147483647#u32 := by scalar_tac
  have nh : ¬h ≥ 2147483647#u32 := by scalar_tac
  simp only [FIo_Native.aspis_core.field.wide_exact.WideExact.from_limbs,
    i0,i1,i2,i3,i4,i5,i6,i7,bind_tc_ok,FIo_Native.aspis_core.field.P,
    if_neg na,if_neg nb,if_neg nc,if_neg nd,if_neg ne,if_neg nf,if_neg ng,if_neg nh] <;> rfl

#print axioms source
end AspisR1.NFS_LPf_WideConstruction
-- END copied LPf_WideConstruction
-- BEGIN copied NBG_WideCarriers
set_option autoImplicit false
noncomputable section
namespace NFS_NBG_WideCarriers
open Aeneas Aeneas.Std Result AspisR1 NFN_LPi_FieldValues

theorem wide_add (x y : NE) (hx : canonE x) (hy : canonE y) :
    ∃ z, FIo_Native.aspis_core.field.wide_exact.WideExact.add x y = ok z ∧
      canonE z ∧ ew z = (addQ (qw x.c0) (qw y.c0), addQ (qw x.c1) (qw y.c1)) := by
  obtain ⟨a,ha,ca,va⟩ := NFS_LPi_TowerValues.qm_add x.c0 y.c0 hx.1 hy.1
  obtain ⟨b,hb,cb,vb⟩ := NFS_LPi_TowerValues.qm_add x.c1 y.c1 hx.2 hy.2
  exact ⟨⟨a,b⟩,by simp only [FIo_Native.aspis_core.field.wide_exact.WideExact.add,
    ha,hb,bind_tc_ok],⟨ca,cb⟩,Prod.ext va vb⟩

theorem limbs_result (a b c d e f g h : U32) :
    FIo_Native.aspis_core.field.wide_exact.WideExact.from_limbs
      (Array.make 8#usize [a,b,c,d,e,f,g,h]) =
      ok (if a < 2147483647#u32 ∧ b < 2147483647#u32 ∧ c < 2147483647#u32 ∧
        d < 2147483647#u32 ∧ e < 2147483647#u32 ∧ f < 2147483647#u32 ∧
        g < 2147483647#u32 ∧ h < 2147483647#u32
        then some (NFS_LPf_WideConstruction.value a b c d e f g h) else none) := by
  simp [FIo_Native.aspis_core.field.wide_exact.WideExact.from_limbs,
    Array.index_usize,Array.make,FIo_Native.aspis_core.field.P,NFS_LPf_WideConstruction.value]
  repeat' split
  all_goals simp_all <;> omega

theorem to_limbs_result (x : NE) :
    FIo_Native.aspis_core.field.wide_exact.WideExact.to_limbs x =
      ok (Array.make 8#usize [x.c0.c0.a,x.c0.c0.b,x.c0.c1.a,x.c0.c1.b,
        x.c1.c0.a,x.c1.c0.b,x.c1.c1.a,x.c1.c1.b]) := rfl

/-- Wrong lengths reject before any byte index, for arbitrary machine slices. -/
theorem wrong_byte_length (bytes : Slice U8) (h : bytes.val.length ≠ 32) :
    FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes bytes = ok none := by
  have hn : Slice.len bytes != 32#usize := by
    simp only [bne_iff_ne]
    intro eq
    have values := congrArg UScalar.val eq
    apply h
    change bytes.val.length = 32 at values
    exact values
  simp only [FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes,
    FIo_Native.aspis_core.field.wide_exact.WideExact.BYTE_LEN,hn,if_true]

abbrev PQ := AspisR1Post25Sampler.field.QM31
abbrev PE := AspisR1Post25Sampler.field.WideExact
def pw (x : PQ) : Nat × Nat × Nat × Nat :=
  (x.c0.a.val,x.c0.b.val,x.c1.a.val,x.c1.b.val)
def reduced (x : PQ) : Nat × Nat × Nat × Nat :=
  (x.c0.a.val%2147483647,x.c0.b.val%2147483647,
   x.c1.a.val%2147483647,x.c1.b.val%2147483647)

theorem remainder (x : U32) : ∃ z, x % 2147483647#u32 = ok z ∧
    z.val = x.val % 2147483647 :=
  WP.spec_imp_exists (UScalar.rem_spec x (y:=2147483647#u32) (by decide))

theorem canonical_qm31 (x : PQ) : ∃ z,
    AspisR1Post25Sampler.field.canonical_qm31 x = ok z ∧ pw z = reduced x := by
  obtain ⟨a,ha,va⟩ := remainder x.c0.a
  obtain ⟨b,hb,vb⟩ := remainder x.c0.b
  obtain ⟨c,hc,vc⟩ := remainder x.c1.a
  obtain ⟨d,hd,vd⟩ := remainder x.c1.b
  refine ⟨⟨⟨a,b⟩,⟨c,d⟩⟩,?_,Prod.ext va (Prod.ext vb (Prod.ext vc vd))⟩
  simp only [AspisR1Post25Sampler.field.canonical_qm31,
    AspisR1Post25Sampler.field.canonical_qm31.closure.Insts.CoreOpsFunctionFnTupleM31M31.call,
    AspisR1Post25Sampler.field.P,ha,hb,hc,hd,bind_tc_ok]

theorem wide_new (x y : PQ) : ∃ z : PE,
    AspisR1Post25Sampler.field.WideExact.new x y = ok z ∧
      (pw z.c0,pw z.c1) = (reduced x,reduced y) := by
  obtain ⟨a,ha,va⟩ := canonical_qm31 x
  obtain ⟨b,hb,vb⟩ := canonical_qm31 y
  exact ⟨⟨a,b⟩,by simp only [AspisR1Post25Sampler.field.WideExact.new,ha,hb,bind_tc_ok],
    Prod.ext va vb⟩

#print axioms wide_add
#print axioms limbs_result
#print axioms to_limbs_result
#print axioms wrong_byte_length
#print axioms remainder
#print axioms canonical_qm31
#print axioms wide_new
end NFS_NBG_WideCarriers
-- END copied NBG_WideCarriers
-- BEGIN copied NBG_FieldDischarge
set_option autoImplicit false
namespace NFS_NBG_FieldDischarge
open Aeneas Aeneas.Std Result AspisR1 NFN_LPi_FieldValues

def modQ (q : QW) : QW :=
  ((q.1.1%2147483647,q.1.2%2147483647),(q.2.1%2147483647,q.2.2%2147483647))
def scaleQ (q : QW) (s : Nat) : QW :=
  ((q.1.1*s%2147483647,q.1.2*s%2147483647),
   (q.2.1*s%2147483647,q.2.2*s%2147483647))

theorem canonical_fio (x : NQ) : ∃ z,
    FIo_Native.aspis_core.field.wide_exact.canonical_qm31 x = ok z ∧
      canonQ z ∧ qw z = modQ (qw x) := by
  obtain ⟨a,ha,va⟩ := NFS_NBG_WideCarriers.remainder x.c0.a
  obtain ⟨b,hb,vb⟩ := NFS_NBG_WideCarriers.remainder x.c0.b
  obtain ⟨c,hc,vc⟩ := NFS_NBG_WideCarriers.remainder x.c1.a
  obtain ⟨d,hd,vd⟩ := NFS_NBG_WideCarriers.remainder x.c1.b
  have ca : a.val<2147483647 := by rw [va]; exact Nat.mod_lt _ (by decide)
  have cb : b.val<2147483647 := by rw [vb]; exact Nat.mod_lt _ (by decide)
  have cc : c.val<2147483647 := by rw [vc]; exact Nat.mod_lt _ (by decide)
  have cd : d.val<2147483647 := by rw [vd]; exact Nat.mod_lt _ (by decide)
  refine ⟨⟨⟨a,b⟩,⟨c,d⟩⟩,?_,⟨⟨ca,cb⟩,⟨cc,cd⟩⟩,
    Prod.ext (Prod.ext va vb) (Prod.ext vc vd)⟩
  simp only [FIo_Native.aspis_core.field.wide_exact.canonical_qm31,
    FIo_Native.aspis_core.field.wide_exact.canonical_qm31.closure.Insts.CoreOpsFunctionFnTupleM31M31.call,
    FIo_Native.aspis_core.field.P,ha,hb,hc,hd,bind_tc_ok]

theorem wide_scale (x : NE) (s : U32) : ∃ z,
    FIo_Native.aspis_core.field.wide_exact.WideExact.mul_m31 x s = ok z ∧
      canonE z ∧ ew z = (scaleQ (qw x.c0) (s.val%2147483647),
        scaleQ (qw x.c1) (s.val%2147483647)) := by
  obtain ⟨r,hr,vr⟩ := NFS_NBG_WideCarriers.remainder s
  obtain ⟨a,ha,ca,va⟩ := NFS_LPi_MixedValues.qm_m31 x.c0 r
  obtain ⟨b,hb,cb,vb⟩ := NFS_LPi_MixedValues.qm_m31 x.c1 r
  refine ⟨⟨a,b⟩,?_,⟨ca,cb⟩,Prod.ext ?_ ?_⟩
  · simp only [FIo_Native.aspis_core.field.wide_exact.WideExact.mul_m31,
      FIo_Native.aspis_core.field.P,hr,ha,hb,bind_tc_ok]
  · simpa only [ew,scaleQ,qw,cw,vr] using va
  · simpa only [ew,scaleQ,qw,cw,vr] using vb

theorem wide_qm (x : NE) (y : NQ) (hx : canonE x) : ∃ z,
    FIo_Native.aspis_core.field.wide_exact.WideExact.mul_qm31 x y = ok z ∧
      canonE z ∧ ew z = (mulQ (qw x.c0) (modQ (qw y)),
        mulQ (qw x.c1) (modQ (qw y))) := by
  obtain ⟨r,hr,cr,vr⟩ := canonical_fio y
  obtain ⟨a,ha,ca,va⟩ := NFS_LPi_TowerValues.qm_mul x.c0 r hx.1 cr
  obtain ⟨b,hb,cb,vb⟩ := NFS_LPi_TowerValues.qm_mul x.c1 r hx.2 cr
  refine ⟨⟨a,b⟩,?_,⟨ca,cb⟩,Prod.ext ?_ ?_⟩
  · simp only [FIo_Native.aspis_core.field.wide_exact.WideExact.mul_qm31,hr,ha,hb,bind_tc_ok]
  · simpa only [ew,vr] using va
  · simpa only [ew,vr] using vb

#print axioms canonical_fio
#print axioms wide_scale
#print axioms wide_qm
#print axioms AspisR1.NFN_LPf_BaseMultiply.source
#print axioms AspisR1.NFN_LPi_FieldValues.cm_mul
#print axioms AspisR1.NFS_LPi_TowerValues.qm_mul
#print axioms AspisR1.NFS_LPi_TowerValues.wide_mul
#print axioms AspisR1.NFS_LPi_TowerValues.mul_u
#print axioms AspisR1.NFS_LPi_MixedValues.cm_m31
#print axioms AspisR1.NFS_LPi_MixedValues.qm_m31
end NFS_NBG_FieldDischarge
-- END copied NBG_FieldDischarge
-- BEGIN copied NEV_MaskCarriers
set_option autoImplicit false
noncomputable section
namespace NFS_NEV_MaskCarriers
open Aeneas Aeneas.Std Result AspisR1
abbrev Native := FIo_Native.aspis_core.field.QM31
abbrev Mask := AspisR1SelectedMaskProbe.field.QM31
abbrev Words := (Nat × Nat) × (Nat × Nat)

def toMask (q : Native) : Mask := ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩
def fromMask (q : Mask) : Native := ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩
theorem native_roundtrip (q : Native) : fromMask (toMask q)=q := by cases q;rfl
theorem mask_roundtrip (q : Mask) : toMask (fromMask q)=q := by cases q;rfl
theorem canonical (q : Native) : NFN_LPi_FieldValues.canonQ q ↔
    ExtractedMaskTowerAdd.CanonicalQM (toMask q) := Iff.rfl
theorem words (q : Native) : ExtractedMaskQM31Mul.wordsQM (toMask q)=NFN_LPi_FieldValues.qw q := rfl
/-- The two imported natural-word product definitions are literally the same
Karatsuba formula. No multiplication theorem is reproved. -/
theorem product_words (x y : Words) : NFN_LPi_FieldValues.mulQ x y=ExtractedMaskQM31Mul.qmMulWords x y := rfl

theorem words_injective (x y : Mask)
    (same : ExtractedMaskQM31Mul.wordsQM x=ExtractedMaskQM31Mul.wordsQM y) : x=y := by
  have a : x.c0.a=y.c0.a := UScalar.eq_of_val_eq (congrArg (fun z : Words=>z.1.1) same)
  have b : x.c0.b=y.c0.b := UScalar.eq_of_val_eq (congrArg (fun z : Words=>z.1.2) same)
  have c : x.c1.a=y.c1.a := UScalar.eq_of_val_eq (congrArg (fun z : Words=>z.2.1) same)
  have d : x.c1.b=y.c1.b := UScalar.eq_of_val_eq (congrArg (fun z : Words=>z.2.2) same)
  exact congrArg₂ AspisR1SelectedMaskProbe.field.QM31.mk
    (congrArg₂ AspisR1SelectedMaskProbe.field.CM31.mk a b)
    (congrArg₂ AspisR1SelectedMaskProbe.field.CM31.mk c d)
theorem native_injective (x y : Native) (same : NFN_LPi_FieldValues.qw x=NFN_LPi_FieldValues.qw y) : x=y := by
  have transported : toMask x=toMask y := words_injective _ _
    (by simpa only [words] using same)
  have result := congrArg fromMask transported
  simpa only [native_roundtrip] using result
#print axioms native_roundtrip
#print axioms mask_roundtrip
#print axioms canonical
#print axioms words
#print axioms product_words
#print axioms words_injective
#print axioms native_injective
end NFS_NEV_MaskCarriers
end
-- END copied NEV_MaskCarriers
-- BEGIN copied NEV_MaskQM
set_option autoImplicit false
noncomputable section
namespace NFS_NEV_MaskQM
open Aeneas Aeneas.Std Result AspisR1 NFS_NEV_MaskCarriers

theorem add (x y : Native) (hx : NFN_LPi_FieldValues.canonQ x) (hy : NFN_LPi_FieldValues.canonQ y) :
    (do let out ← FIo_Native.aspis_core.field.QM31.add x y;ok (toMask out)) =
      AspisR1SelectedMaskProbe.field.QM31.add (toMask x) (toMask y) := by
  obtain ⟨native,hn,cn,vn⟩ := NFS_LPi_TowerValues.qm_add x y hx hy
  obtain ⟨mask,hm,cm,vm⟩ := ExtractedMaskTowerAdd.current_qm_add_mod
    (toMask x) (toMask y) ((canonical x).mp hx) ((canonical y).mp hy)
  have maskValue : ExtractedMaskQM31Mul.wordsQM mask=NFN_LPi_FieldValues.addQ (NFN_LPi_FieldValues.qw x) (NFN_LPi_FieldValues.qw y) := vm
  have same := words_injective (toMask native) mask
    (by simpa only [words] using vn.trans maskValue.symm)
  simp only [hn,hm,bind_tc_ok,same]

theorem multiply (x y : Native) (hx : NFN_LPi_FieldValues.canonQ x) (hy : NFN_LPi_FieldValues.canonQ y) :
    (do let out ← FIo_Native.aspis_core.field.QM31.mul x y;ok (toMask out)) =
      AspisR1SelectedMaskProbe.field.QM31.mul (toMask x) (toMask y) := by
  obtain ⟨native,hn,cn,vn⟩ := NFS_LPi_TowerValues.qm_mul x y hx hy
  obtain ⟨mask,hm,cm,vm⟩ := ExtractedMaskQM31Mul.current_qm_mul_words
    (toMask x) (toMask y) ((canonical x).mp hx) ((canonical y).mp hy)
  have maskValue : ExtractedMaskQM31Mul.wordsQM mask=NFN_LPi_FieldValues.mulQ (NFN_LPi_FieldValues.qw x) (NFN_LPi_FieldValues.qw y) := by
    rw [product_words]
    exact vm
  have same := words_injective (toMask native) mask
    (by simpa only [words] using vn.trans maskValue.symm)
  simp only [hn,hm,bind_tc_ok,same]

/-- Reuse the retained all-word normalization value law; canonicality of this
actual argument makes each already-proved remainder an identity. -/
theorem normalization (q : Native) (hq : NFN_LPi_FieldValues.canonQ q) :
    FIo_Native.aspis_core.field.wide_exact.canonical_qm31 q=ok q := by
  obtain ⟨out,run,canonicalOut,value⟩ := NFS_NBG_FieldDischarge.canonical_fio q
  have sameWords : NFN_LPi_FieldValues.qw out=NFN_LPi_FieldValues.qw q := by
    simpa only [NFS_NBG_FieldDischarge.modQ,NFN_LPi_FieldValues.qw,NFN_LPi_FieldValues.cw,
      Nat.mod_eq_of_lt hq.1.1,Nat.mod_eq_of_lt hq.1.2,
      Nat.mod_eq_of_lt hq.2.1,Nat.mod_eq_of_lt hq.2.2] using value
  exact run.trans (congrArg Result.ok (native_injective out q sameWords))
#print axioms add
#print axioms multiply
#print axioms normalization
end NFS_NEV_MaskQM
end
-- END copied NEV_MaskQM
-- BEGIN copied NEV_StageFields
set_option autoImplicit false
noncomputable section
namespace NFS_NEV_StageFields
open Aeneas Aeneas.Std Result AspisR1
abbrev Q := NBF_RowInstall.Q
abbrev E := NBF_RowInstall.E
abbrev NQ := NFS_NEV_MaskCarriers.Native
abbrev NE := FIo_Native.aspis_core.field.wide_exact.WideExact

def nq (q : Q) : NQ := ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩
def sq (q : NQ) : Q := ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩
def ne (e : E) : NE := ⟨nq e.c0,nq e.c1⟩
def se (e : NE) : E := ⟨sq e.c0,sq e.c1⟩
theorem native_q_roundtrip (q : NQ) : nq (sq q)=q := by cases q;rfl
theorem stage_q_roundtrip (q : Q) : sq (nq q)=q := by cases q;rfl
theorem native_e_roundtrip (e : NE) : ne (se e)=e := by cases e;rfl
theorem stage_e_roundtrip (e : E) : se (ne e)=e := by cases e;rfl

theorem canonical_q (q : Q) : NBF_PowerStep.Canonical q ↔ NFN_LPi_FieldValues.canonQ (nq q) :=
  (NBO_FieldPorts.canonicalQ q).trans (NFS_NEV_MaskCarriers.canonical (nq q)).symm
theorem canonical_e (e : E) : NBO_TailDomain.WideCanonical e ↔ NFN_LPi_FieldValues.canonE (ne e) :=
  and_congr (canonical_q e.c0) (canonical_q e.c1)

/-- Actual emitted QM31 call agrees with the already adopted NBO scalar
callback. Both totality/value laws are imported, never arithmetic in Kani. -/
theorem power (x y : Q) (hx : NBF_PowerStep.Canonical x) (hy : NBF_PowerStep.Canonical y) :
    (do let out ← FIo_Native.aspis_core.field.QM31.mul (nq x) (nq y);ok (sq out)) =
      NBO_FieldSemantics.power x y := by
  have same := NFS_NEV_MaskQM.multiply (nq x) (nq y) ((canonical_q x).mp hx) ((canonical_q y).mp hy)
  have lifted := congrArg (fun result : Result NFS_NEV_MaskCarriers.Mask =>
    do let out ← result;ok (NBO_FieldPorts.fromQ out)) same
  simpa only [NBO_FieldSemantics.power,NBO_FieldPorts.toQ,NBO_FieldPorts.fromQ,
    NFS_NEV_MaskCarriers.toMask,nq,sq,bind_assoc_eq,bind_tc_ok] using lifted
#print axioms native_q_roundtrip
#print axioms stage_q_roundtrip
#print axioms native_e_roundtrip
#print axioms stage_e_roundtrip
#print axioms canonical_q
#print axioms canonical_e
#print axioms power
end NFS_NEV_StageFields
end
-- END copied NEV_StageFields

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
