import R1Z.PV_RunJoin_HonestIdentification26
import R1Z.BuilderRecordsArray
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_FrontierHonesty28
open Aeneas Aeneas.Std Result PV_Src_NativeInput
open BuilderForestAdmissionPort BuilderForestAdmissionPort.pool_v1
open PV_RunJoin_FixtureArguments
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]

/-- A raw word equal to P cannot be a canonical frontier word. This rules
out HonestInput independently of every cached/returned compilation field. -/
theorem noncanonical_excludes (i : Input)
    (raw : i.snapshot.frontier.val[0]!.val[0]!.val = 2147483647) :
    ¬ PV_RunJoin_ConsumerBoundary25.HonestInput (K := K) i := by
  intro h
  have hc := h.2.2.2 (⟨0,by decide⟩ : Fin 20) 0 (by decide)
  change i.snapshot.frontier.val[0]!.val[0]!.val < 2147483647 at hc
  rw [raw] at hc
  omega
#print axioms noncanonical_excludes

def rawDigest : Array U32 8#usize :=
  BuilderRecordsArray.tabulate 8#usize (fun _ => 2147483647#u32)
def frontier : Array (Array U32 8#usize) 20#usize :=
  BuilderRecordsArray.tabulate 20#usize
    (fun l => if l = 0 then rawDigest else snapshot.frontier.val[l]!)

theorem raw_word : frontier.val[0]!.val[0]!.val = 2147483647 := by
  have outer : frontier.val[0]! = rawDigest :=
    BuilderRecordsArray.tabulate_get 20#usize _ 0 (by decide)
  rw [outer]
  have inner : rawDigest.val[0]! = 2147483647#u32 :=
    BuilderRecordsArray.tabulate_get 8#usize _ 0 (by decide)
  rw [inner]
  rfl
#print axioms raw_word

/-- Exact argument shape of the focused native guard probe. The root and
payload are quantified: no hand-edited cached payload is used. -/
def input (root : Array U32 8#usize)
    (compiled : pair_forest_trace.PoolV1PairForestMergedC1CompilationV1) : Input :=
  ⟨withdrawalRequest,witness,withdrawalChange,laneAnchor,
    { snapshot with
      sequence := 1#u64
      next_pair_index := 1#u64
      current_root := root
      frontier := frontier },compiled⟩

theorem every_payload_not_honest (root : Array U32 8#usize)
    (compiled : pair_forest_trace.PoolV1PairForestMergedC1CompilationV1) :
    ¬ PV_RunJoin_ConsumerBoundary25.HonestInput (K := K) (input root compiled) :=
  noncanonical_excludes _ raw_word
#print axioms every_payload_not_honest
end R1Z.PV_RunJoin_FrontierHonesty28
