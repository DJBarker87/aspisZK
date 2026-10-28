import R1Z.BuilderForestAdmissionPort
import R1Z.PV_RunJoin_HonestIdentification26
import R1Z.PV_Src_CompilerTactic
import R1Z.PV_Src_CanonicalSnapshot
import R1Z.PV_RunJoin_FrontierHonesty28
set_option autoImplicit false
noncomputable section

namespace R1Z.PV_RunJoin_ActiveFrontier28
open Aeneas Aeneas.Std Result
open BuilderForestAdmissionPort BuilderForestAdmissionPort.pool_v1

/-- At index one, the actual extracted tree frontier-validation loop skips
slot zero completely. This is a single symbolic loop step, not an evaluation
of a hash or a whole preparation. -/
theorem active_slot_skipped
    (frontier : Array (Array U32 8#usize) 20#usize)
    (empty : Array (Array U32 8#usize) 21#usize) :
    incremental_merkle.tree_reference.validate_owned_loop
      1#u64 frontier empty (.Ok ()) 0#usize =
    incremental_merkle.tree_reference.validate_owned_loop
      1#u64 frontier empty (.Ok ()) 1#usize := by
  conv_lhs => rw [incremental_merkle.tree_reference.validate_owned_loop]
  simp only [format.POOL_V1_TREE_DEPTH]
  rw [if_pos (by decide)]
  simp only [core.result.Result.is_ok,bind_tc_ok,lift,Bool.true_eq,if_true]
  have shifted : (BuilderStdModels.shift64 1#u64 0#usize).val = 1 := by
    rw [BuilderStdModels.shift64_spec]
    change ((1#u64).bv.ushiftRight ((0#usize).val % 64)).toNat = 1
    simp only [UScalar.ofNatCore_val_eq,Nat.zero_mod,BitVec.toNat_ushiftRight]
    rfl
  have active : BuilderStdModels.shift64 1#u64 0#usize &&& 1#u64 ≠ 0#u64 := by
    intro h
    have words := congrArg UScalar.val h
    rw [UScalar.val_and,shifted] at words
    change 1 = 0 at words
    omega
  rw [if_neg active]
  have next : Usize.wrapping_add 0#usize 1#usize = 1#usize := by
    apply UScalar.eq_of_val_eq
    rw [R0Z.WriterRefine.uadd _ _ (by simp)]
    rfl
  rw [next]
#print axioms active_slot_skipped
end R1Z.PV_RunJoin_ActiveFrontier28
namespace R1Z.PV_RunJoin_PreparedPayload28
open Aeneas Aeneas.Std Result PV_Src_NativeInput
open BuilderForestAdmissionPort BuilderForestAdmissionPort.pool_v1
local notation "E" => PV_RunJoin_ShippedExternal.E_shipped
local notation "R" => PV_RunJoin_UniversalRecords22.shipped

/-- Inputs of the extracted inner compiler, with no cached output field. -/
structure Arguments where
  request : Request
  witness : pair_forest_trace.PoolV1PairForestInputNoteWitnessV1
  change : payment_relation.PoolV1OutputNoteWitnessV1
  laneAnchor : Array U32 8#usize
  snapshot : pair_tree_profile.PoolV1PairLiveSnapshotV1

def install (a : Arguments)
    (c : pair_forest_trace.PoolV1PairForestMergedC1CompilationV1) : Input :=
  ⟨a.request,a.witness,a.change,a.laneAnchor,a.snapshot,c⟩

def call (a : Arguments) := @pair_forest_trace.compile_forest_from_copies E R
  a.witness (outputValue a.request) (recipient a.request) a.change
  (forestPublic a.request) a.laneAnchor a.snapshot

/-- Proof-local packaging of the compiler's actual return. This adds no
validation and is not substituted for either Rust preparation wrapper. -/
def package (a : Arguments) : Result (core.result.Result Input pair_trace.PoolV1PairTraceErrorV1) := do
  let result ← call a
  match result with
  | .Ok c => ok (.Ok (install a c))
  | .Err e => ok (.Err e)

/-- Successful packaging fixes the complete returned payload and both Result
layers. Admission and representation validity are not inferred here. -/
theorem cached_return (a : Arguments) (i : Input)
    (h : package a = ok (.Ok i)) :
    @run E R i = ok (.Ok i.compiled) := by
  unfold package at h
  pv_peel h with result hr
  cases result with
  | Ok c =>
    cases Result.ok.inj h
    exact hr
  | Err e => cases h
#print axioms cached_return

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]

/-- Exact remaining obligations after actual successful output packaging;
none is hidden in the payload type or equated with SourceIdentification. -/
theorem honest_iff (a : Arguments) (i : Input)
    (h : package a = ok (.Ok i)) :
    PV_RunJoin_ConsumerBoundary25.HonestInput (K := K) i ↔
      PV_RunJoin_UniversalBuild22.Admission (K := K) i ∧
      PV_Src_RecordReference.Checked i ∧
      ∀ l : Fin 20, R0Z.WriterRefine.Canon8 i.snapshot.frontier.val[l.val]! := by
  constructor
  · exact fun hi => ⟨hi.1,hi.2.2⟩
  · exact fun hi => ⟨hi.1,cached_return a i h,hi.2⟩
#print axioms honest_iff
end R1Z.PV_RunJoin_PreparedPayload28
namespace R1Z.PV_RunJoin_CanonicalFrontier28
open Aeneas Aeneas.Std Result R0Z.WriterRefine R1J.SpendWitnessMap
open PV_Src_NativeInput

/-- Canonical encoding supplies the frontier fact before compilation. The
association must be proved for the actual preparation inputs; successful
compilation by itself cannot replace it. Only frontier equality is needed. -/
theorem frontier_of_encoding (i : Input) (pub : R0P.Public F)
    (bound : pub.nextPairIndex < 2^64)
    (pool domain : PV_Src_PublicRecords.Context)
    (encoded : i.snapshot.frontier = (PV_Src_CanonicalSnapshot.native pub bound pool domain).frontier)
    (l : Fin 20) : Canon8 i.snapshot.frontier.val[l.val]! := by
  rw [encoded]
  exact PV_Src_CanonicalSnapshot.frontier_canonical pub bound pool domain l
#print axioms frontier_of_encoding

theorem probe_excluded_by_encoding (pub : R0P.Public F)
    (bound : pub.nextPairIndex < 2^64) (pool domain : PV_Src_PublicRecords.Context) :
    PV_RunJoin_FrontierHonesty28.frontier ≠
      (PV_Src_CanonicalSnapshot.native pub bound pool domain).frontier := by
  intro same
  have hc := PV_Src_CanonicalSnapshot.frontier_canonical pub bound pool domain
    (⟨0,by decide⟩ : Fin 20) 0 (by decide)
  rw [← same] at hc
  change PV_RunJoin_FrontierHonesty28.frontier.val[0]!.val[0]!.val < 2147483647 at hc
  rw [PV_RunJoin_FrontierHonesty28.raw_word] at hc
  omega
#print axioms probe_excluded_by_encoding
end R1Z.PV_RunJoin_CanonicalFrontier28
