import OraclePortShortCircuitDecision

/-! Strengthens the small schedule cut to the actual height-18 selected slot.
For q=0 all ten source keys are duplicates. candidate.rs:180-188 necessarily
hashes opening 0 then opening 1 before it can reject the duplicate. Existing
verifySlot hashes opening 0 then its first parent before any duplicate.
We quantify over every possible source continuation after those first two
reads; no extraction equality or upstream stored-proof reachability is assumed. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortShortCircuitSlotObstruction
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open OracleDecisionMultiTree OracleDecisionMultiBuild
open OraclePortCompactDraft OraclePortSelectedDraft OraclePortBatchDraft
attribute [local instance] Classical.propDecidable
attribute [local irreducible] verifySlot tree

def spine (a : Bytes) (s : Nat → State) : Nat → Tree
  | 0 => .opened a
  | h+1 => .branch (spine a s h) (.supplied (s h))

theorem unoccupied (is : List Nat) (f : Nat → Bytes) (s : Nat → Nat → State)
    (h b : Nat) (no : ¬ Occupied is h b) :
    build is f s h b = .supplied (s h b) := by
  cases h <;> simp only [build,if_neg no]

theorem zero_build (is : List Nat) (f : Nat → Bytes) (s : Nat → Nat → State)
    (mem : 0 ∈ is) (allZero : ∀ i ∈ is, i = 0) (h : Nat) :
    build is f s h 0 = spine (f 0) (fun k => s k (2^k)) h := by
  have occ (k : Nat) : Occupied is k 0 :=
    ⟨0,mem,le_rfl,by simpa using (Nat.pow_pos (by decide : 0 < 2) : 0 < 2^k)⟩
  induction h with
  | zero => simp only [build,if_pos (occ 0),spine]
  | succ h ih =>
    have no : ¬ Occupied is h (2^h) := by
      rintro ⟨i,hi,lo,_⟩
      have eq := allZero i hi
      have pos : 0 < 2^h := Nat.pow_pos (by decide)
      omega
    simp only [build,if_pos (occ (h+1)),Nat.zero_add,ih,spine]
    rw [unoccupied is f s h (2^h) no]

theorem spine_first_two (a : Bytes) (s : Nat → State) (H : Bytes → State) (h : Nat) :
    ∃ tail, (eval H (OraclePortBatchDraft.execute (spine a s (h+1)))).1 =
      (a,H a) :: (BinMerkle32Path.nodeInput (children (H a) (s 0)),
        H (BinMerkle32Path.nodeInput (children (H a) (s 0)))) :: tail := by
  induction h with
  | zero => exact ⟨[],rfl⟩
  | succ h ih =>
    obtain ⟨tail,eq⟩ := ih
    rw [spine]
    simp only [OraclePortBatchDraft.execute,eval_bind,eval,List.append_nil]
    rw [eq]
    exact ⟨_,rfl⟩

def zeroQueries : Fin 22 → Fin 262144 := fun _ => 0

theorem zero_selected : selected zeroQueries 0 0 = List.replicate 10 0 := by
  have idx (pos : Nat) : OraclePortSelectedDraft.index zeroQueries 0 pos = 0 := by
    simp [OraclePortSelectedDraft.index,zeroQueries]
  change (List.range 10).map (OraclePortSelectedDraft.index zeroQueries 0) = _
  rw [show OraclePortSelectedDraft.index zeroQueries 0 = (fun _ => 0) from funext idx]
  simp

theorem zero_input (p : Parsed) : input p zeroQueries 0 0 0 = leaf p 0 0 := by
  unfold input position
  have first : ((batchPositions 0).find? (fun pos => decide (index zeroQueries 0 pos = 0))) = some 0 := by
    simp [batchPositions,index,zeroQueries]
  rw [first]
  rfl

theorem slot_first_two (p : Parsed) (H : Bytes → State) :
    ∃ parent rest, (eval H (verifySlot p zeroQueries 0 0)).1 =
      (leaf p 0 0,H (leaf p 0 0)) ::
        (BinMerkle32Path.nodeInput parent,H (BinMerkle32Path.nodeInput parent)) :: rest := by
  have shape := zero_build (selected zeroQueries 0 0) (input p zeroQueries 0 0)
    (sibling p zeroQueries 0 0)
    (by rw [zero_selected]; simp)
    (by rw [zero_selected]; intro i hi; simpa using hi) 18
  rw [zero_input] at shape
  have two := spine_first_two (leaf p 0 0) (fun k => sibling p zeroQueries 0 0 k (2^k)) H 17
  rw [← shape] at two
  obtain ⟨tail,eq⟩ := two
  simp only [verifySlot,tree,eval_bind,eval,List.append_nil]
  rw [eq]
  exact ⟨_,_,rfl⟩

/-- Exact source first-two-read cut for the all-zero query batch, with any
remaining duplicate/padding/parent/error continuation. -/
def sourceFirstTwo (p : Parsed) (next : State → State → Program Bytes State Bool) :
    Program Bytes State Bool :=
  Program.ask (leaf p 0 0) fun d0 => Program.ask (leaf p 0 1) fun d1 => next d0 d1

theorem actual_slot_not_prefix (p : Parsed) (H : Bytes → State)
    (next : State → State → Program Bytes State Bool) :
    ¬ (eval H (sourceFirstTwo p next)).1 <+:
      (eval H (verifySlot p zeroQueries 0 0)).1 := by
  intro hp
  obtain ⟨parent,rest,model⟩ := slot_first_two p H
  obtain ⟨suffix,eq⟩ := hp
  rw [model] at eq
  have second := congrArg (fun xs => (xs[1]?).map Prod.fst) eq
  simp only [sourceFirstTwo,eval,List.cons_append,List.getElem?_cons_succ,
    List.getElem?_cons_zero,Option.map_some,Option.some.injEq] at second
  have head := congrArg List.head? second
  change some (0x10 : AspisV8R19.DuplexFrames.Byte) = some 0x12 at head
  contradiction

#print axioms unoccupied
#print axioms zero_build
#print axioms spine_first_two
#print axioms zero_selected
#print axioms zero_input
#print axioms slot_first_two
#print axioms actual_slot_not_prefix
end AspisR1.OraclePortShortCircuitSlotObstruction
end
