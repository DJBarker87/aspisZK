import Port12COUNT_Batch
import Port9OR_Installed
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port12COUNT_Installed
open Aeneas Aeneas.Std Result VTop_Stages
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

 theorem batch0 {Hash : Type} (D : aspis_core.digest.Digest32 Hash) (hash : Hash) (H : Bytes → State)
    (proof : Slice U8) (p : verifier.Prepared) (folded : Array U8 32#usize) :
    (eval H (Port9OR_Installed.batch D hash proof p folded 0#usize)).1.length≤477 := by
  unfold Port9OR_Installed.batch Port9OR_Installed.code
  have joined := Port12COUNT_Verify.bind_count (VTop_Checkpoint.digest D) hash H
    (Port9OR_Batch.code Port4B_Install.leaves (VTop_Checkpoint.digest D) hash proof p folded 0#usize)
    (fun out => pure (match out with | .Ok a => .Ok a | .Err e => .Err (Port3_CheckpointInstall.error e)))
    477 0 (Port12COUNT_Batch.batch0 _ _ _ _ _ _ _) (by intro out _; cases out <;> exact Nat.zero_le 0)
  exact joined

theorem batch1 {Hash : Type} (D : aspis_core.digest.Digest32 Hash) (hash : Hash) (H : Bytes → State)
    (proof : Slice U8) (p : verifier.Prepared) (folded : Array U8 32#usize) :
    (eval H (Port9OR_Installed.batch D hash proof p folded 1#usize)).1.length≤563 := by
  unfold Port9OR_Installed.batch Port9OR_Installed.code
  have joined := Port12COUNT_Verify.bind_count (VTop_Checkpoint.digest D) hash H
    (Port9OR_Batch.code Port4B_Install.leaves (VTop_Checkpoint.digest D) hash proof p folded 1#usize)
    (fun out => pure (match out with | .Ok a => .Ok a | .Err e => .Err (Port3_CheckpointInstall.error e)))
    563 0 (Port12COUNT_Batch.batch1 _ _ _ _ _ _ _) (by intro out _; cases out <;> exact Nat.zero_le 0)
  exact joined

/-- Exact installed calls, arbitrary states and outcomes. This bounds the sum
of the four owned call logs, not an arbitrary rest implementation's log. -/
theorem owned_calls (ops : Ops) (reserved : Bool) (unwrap : Port6CK_Semantic.Unwrap)
    (rest : VTop_OracleCode.Implementation) {Hash : Type} (D : aspis_core.digest.Digest32 Hash)
    (hash : Hash) (H : Bytes → State) (proof pub ck : Slice U8)
    (p0 p1 : verifier.Prepared) (written : verifier.Accumulator)
    (folded0 folded1 : Array U8 32#usize) :
    let impl := Port9OR_Installed.implementation ops reserved unwrap rest
    (eval H (impl (.op5 D proof p0 folded0 0#usize hash))).1.length +
    (eval H (impl (.op8 D p0 written proof pub hash))).1.length +
    (eval H (impl (.op18 D ck proof pub .S2 hash))).1.length +
    (eval H (impl (.op5 D proof p1 folded1 1#usize hash))).1.length ≤1046 := by
  have b0 := batch0 D hash H proof p0 folded0
  have b1 := batch1 D hash H proof p1 folded1
  have writer := Port11PROV_SourceCount.writer_count D hash H p0 written proof pub
  have reader := Port9OR_Budget.reader_count reserved unwrap D ck proof pub .S2 hash H
  change (eval H (Port9OR_Installed.batch D hash proof p0 folded0 0#usize)).1.length+
    (eval H (Port9OR_Bodies.writer D p0 written proof pub hash)).1.length+
    (eval H (Port9OR_Bodies.reader reserved unwrap D ck proof pub .S2 hash)).1.length+
    (eval H (Port9OR_Installed.batch D hash proof p1 folded1 1#usize)).1.length≤1046
  omega

theorem program_bind_bound {A B : Type} (H : Bytes → State) (p : Program Bytes State A)
    (next : A → Program Bytes State B) (n m : Nat)
    (first : (eval H p).1.length≤n) (tail : ∀ a, (eval H (next a)).1.length≤m) :
    (eval H (bind p next)).1.length≤n+m := by
  rw [eval_bind,List.length_append]
  have rest := tail (eval H p).2
  omega

/-- Concrete owned-call projection with the actual writer's saved Vec feeding
current18, and its reply's Prepared feeding batch1. Delegated driver calls are
not included; no whole-driver/source1161 claim is made. -/
def checkpointChain (reserved : Bool) (unwrap : Port6CK_Semantic.Unwrap) {Hash : Type}
    (D : aspis_core.digest.Digest32 Hash) (hash : Hash) (proof pub : Slice U8)
    (p0 : verifier.Prepared) (written : verifier.Accumulator) (folded0 folded1 : Array U8 32#usize) :
    Program Bytes State Bool :=
  bind (Port9OR_Installed.batch D hash proof p0 folded0 0#usize) fun first => match first with
  | .ok (.Ok _) =>
    bind (Port9OR_Bodies.writer D p0 written proof pub hash) fun wrote => match wrote with
    | .ok saved =>
      bind (Port9OR_Bodies.reader reserved unwrap D saved.deref proof pub .S2 hash) fun resumed => match resumed with
      | .ok (.Ok (p1,_)) => bind (Port9OR_Installed.batch D hash proof p1 folded1 1#usize)
          fun final => .done (Port1_Driver.verdict final)
      | _ => .done false
    | _ => .done false
  | _ => .done false

theorem checkpointChain_count (reserved : Bool) (unwrap : Port6CK_Semantic.Unwrap) {Hash : Type}
    (D : aspis_core.digest.Digest32 Hash) (hash : Hash) (H : Bytes → State) (proof pub : Slice U8)
    (p0 : verifier.Prepared) (written : verifier.Accumulator) (folded0 folded1 : Array U8 32#usize) :
    (eval H (checkpointChain reserved unwrap D hash proof pub p0 written folded0 folded1)).1.length≤1046 := by
  unfold checkpointChain
  apply program_bind_bound H _ _ 477 569 (batch0 D hash H proof p0 folded0)
  intro first
  cases first with
  | fail e => exact Nat.zero_le _
  | div => exact Nat.zero_le _
  | ok result =>
    cases result with
    | Err e => exact Nat.zero_le _
    | Ok unit =>
      apply program_bind_bound H _ _ 3 566 (Port11PROV_SourceCount.writer_count D hash H p0 written proof pub)
      intro wrote
      cases wrote with
      | fail e => exact Nat.zero_le _
      | div => exact Nat.zero_le _
      | ok saved =>
        apply program_bind_bound H _ _ 3 563 (Port9OR_Budget.reader_count reserved unwrap D saved.deref proof pub .S2 hash H)
        intro resumed
        cases resumed with
        | fail e => exact Nat.zero_le _
        | div => exact Nat.zero_le _
        | ok result =>
          cases result with
          | Err e => exact Nat.zero_le _
          | Ok pair =>
            obtain ⟨p1,a1⟩ := pair
            exact program_bind_bound H _ _ 563 0 (batch1 D hash H proof p1 folded1) (fun _ => Nat.zero_le 0)

#print axioms batch0
#print axioms batch1
#print axioms owned_calls
#print axioms program_bind_bound
#print axioms checkpointChain_count
end AspisR1.Port12COUNT_Installed
end
