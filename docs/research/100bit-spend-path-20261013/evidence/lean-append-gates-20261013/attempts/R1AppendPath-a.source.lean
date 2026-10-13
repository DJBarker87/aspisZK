import R1AppendNode
import R1AppendCopyLinks

/-! The twenty literal append gates determine a public root and carry node.
The recurrence uses the frozen empty-root table exactly as the gates do;
its equality with recursively generated empty roots is a separate obligation.
No exclusion of the full-tree last insertion is introduced. -/
set_option autoImplicit false
namespace AspisR1.AppendPath
open R0P
variable {K : Type} [Field K]

def block (level : Fin 21) : Fin 57 := ⟨33 + level.val, by omega⟩

theorem bit_zero_or_one (n : Nat) : n &&& 1 = 0 ∨ n &&& 1 = 1 := by
  have h : n &&& 1 = (n.testBit 0).toNat := by simpa using Nat.and_two_pow n 0
  rw [h]
  cases n.testBit 0 <;> simp

def step (pub : Public K) (level : Fin 20) (cur : Digest K) : Digest K :=
  if digestBitZero pub level then nodeCompress cur (AppendNode.frozenEmpty level.castSucc)
  else nodeCompress (pub.snapshotFrontier level) cur

def prefix (pub : Public K) (leaf : Digest K) : Nat → Digest K
  | 0 => leaf
  | n+1 => if h : n < 20 then step pub ⟨n, h⟩ (prefix pub leaf n)
    else prefix pub leaf n

theorem gate_step (prime : Nat) [CharP K prime] (hprime : prime = 2^31-1)
    (pub : Public K) (A : Trace K) (hs : Holds scheduleFamily pub A)
    (hd : Holds digestFamily pub A) (hpo : Holds poseidonScalarFamily pub A)
    (hb : CopyLinkBalance pub A) (level : Fin 20) :
    OutputNotes.output A (block level.succ) =
      step pub level (OutputNotes.output A (block level.castSucc)) := by
  have hnode : ScheduleNode (block level.succ).val := by
    right
    dsimp [block]
    omega
  rw [AppendNode.node_step pub A hs hpo (block level.succ) hnode]
  have hcopy := AppendCopyLinks.append_cells pub A hb level
  have hbound := (digest_holds_iff pub A).mp hd |>.2.2.2.2.1 level
  unfold step
  by_cases hzero : digestBitZero pub level
  · rw [if_pos hzero]
    have hl : AppendNode.left A (block level.succ) =
        OutputNotes.output A (block level.castSucc) := by
      funext i
      exact (hcopy.1 hzero i).symm
    have hr : AppendNode.right A (block level.succ) =
        AppendNode.frozenEmpty level.castSucc := by
      funext i
      have he := hbound.1 hzero i
      change A ⟨8 + i.val, by omega⟩ (g2Row ⟨34 + level.val, by omega⟩ 0) +
        (if i.val = 7 then (1051521018 : K) else 0) = _
      rw [he]
      exact AppendNode.empty_target_untweak prime hprime level i
    rw [hl, hr]
  · rw [if_neg hzero]
    have hone : ((pub.nextPairIndex >>> level.val) &&& 1) = 1 :=
      (bit_zero_or_one (pub.nextPairIndex >>> level.val)).resolve_left hzero
    have hl : AppendNode.left A (block level.succ) = pub.snapshotFrontier level := by
      funext i
      exact hbound.2 hzero i
    have hr : AppendNode.right A (block level.succ) =
        OutputNotes.output A (block level.castSucc) := by
      funext i
      exact (hcopy.2 hone i).symm
    rw [hl, hr]

theorem prefix_output (prime : Nat) [CharP K prime] (hprime : prime = 2^31-1)
    (pub : Public K) (A : Trace K) (hs : Holds scheduleFamily pub A)
    (hd : Holds digestFamily pub A) (hpo : Holds poseidonScalarFamily pub A)
    (hb : CopyLinkBalance pub A) (n : Nat) (hn : n ≤ 20) :
    prefix pub (OutputNotes.output A 33) n = OutputNotes.output A (block ⟨n, by omega⟩) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hn' : n < 20 := by omega
    rw [prefix, dif_pos hn', ih (by omega)]
    exact (gate_step prime hprime pub A hs hd hpo hb ⟨n, hn'⟩).symm

theorem next_root (prime : Nat) [CharP K prime] (hprime : prime = 2^31-1)
    (pub : Public K) (A : Trace K) (hs : Holds scheduleFamily pub A)
    (hd : Holds digestFamily pub A) (hpo : Holds poseidonScalarFamily pub A)
    (hb : CopyLinkBalance pub A) :
    pub.nextRoot = prefix pub (OutputNotes.output A 33) 20 := by
  rw [prefix_output prime hprime pub A hs hd hpo hb 20 (by omega)]
  funext i
  exact ((digest_holds_iff pub A).mp hd |>.2.2.2.2.2.1 i).symm

theorem next_frontier_carry (prime : Nat) [CharP K prime] (hprime : prime = 2^31-1)
    (pub : Public K) (A : Trace K) (hs : Holds scheduleFamily pub A)
    (hd : Holds digestFamily pub A) (hpo : Holds poseidonScalarFamily pub A)
    (hb : CopyLinkBalance pub A) (hc : digestCarry pub.nextPairIndex < 20) :
    pub.nextFrontier ⟨digestCarry pub.nextPairIndex, hc⟩ =
      prefix pub (OutputNotes.output A 33) (digestCarry pub.nextPairIndex) := by
  rw [prefix_output prime hprime pub A hs hd hpo hb _ (digest_carry_le pub.nextPairIndex)]
  funext i
  exact ((digest_holds_iff pub A).mp hd |>.2.2.2.2.2.2 hc i).symm

#print axioms gate_step
#print axioms next_root
#print axioms next_frontier_carry
end AspisR1.AppendPath
