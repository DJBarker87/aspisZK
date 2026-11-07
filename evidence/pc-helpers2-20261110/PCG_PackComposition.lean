import PCG_PackLaw
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace PCG_PackComposition

def writeRange (seed : Nat → Nat) (offset : Nat) (value : Nat → Nat) : Nat → (Nat → Nat)
 | 0 => seed
 | n+1 => Function.update (writeRange seed offset value n) (offset+n) (value (offset+n))

/-- One arbitrary write plus an induction over the untouched frame. -/
theorem writeRange_exact (seed value : Nat → Nat) (offset len index : Nat) :
 writeRange seed offset value len index =
 if offset ≤ index ∧ index < offset+len then value index else seed index := by
 induction len with
 | zero => simp [writeRange]
 | succ n ih =>
   by_cases same : index=offset+n
   · subst index
     simp [writeRange,Function.update]
   · have neq : offset+n ≠ index := Ne.symm same
     simp only [writeRange,Function.update_of_ne same,ih]
     by_cases inside : offset ≤ index ∧ index < offset+n
     · have inside' : offset ≤ index ∧ index < offset+(n+1) := by omega
       rw [if_pos inside,if_pos inside']
     · have outside : ¬ (offset ≤ index ∧ index < offset+(n+1)) := by omega
       rw [if_neg inside,if_neg outside]

def chunks (digest : Array U8 32#usize) : Nat → (Nat → Nat)
 | 0 => fun _ => 0
 | n+1 => writeRange (chunks digest n) (8*n) (PCG_PackLaw.pack digest) 8

/-- The four source chunks compose by disjointness, rather than replaying the
224-bit read / 32-byte write buffer in Kani. -/
theorem chunk_induction (digest : Array U8 32#usize) (n index : Nat) :
 chunks digest n index = if index < 8*n then PCG_PackLaw.pack digest index else 0 := by
 induction n with
 | zero => simp [chunks]
 | succ n ih =>
   rw [chunks,writeRange_exact,ih]
   by_cases older : index < 8*n
   · have outside : ¬ (8*n ≤ index ∧ index < 8*n+8) := by omega
     have within : index < 8*(n+1) := by omega
     rw [if_neg outside,if_pos older,if_pos within]
   · by_cases here : 8*n ≤ index ∧ index < 8*n+8
     · have within : index < 8*(n+1) := by omega
       rw [if_pos here,if_pos within]
     · have beyond : ¬ index < 8*(n+1) := by omega
       rw [if_neg here,if_neg older,if_neg beyond]

/-- Full source word-loop result, from the empty accumulator at any chunk. -/
theorem chunk_word (digest : Array U8 32#usize) (chunk : Nat) :
 ∃ out, PCG_PackLaw.readWord 0#u64 ((digest.val.drop (7*chunk)).take 7) = ok out ∧
 out.val = PCG_PackLaw.word ((digest.val.drop (7*chunk)).take 7) := by
 apply PCG_PackLaw.read_suffix _ 0#u64 0
 · simp only [Nat.zero_add]
   exact Nat.le_trans (List.length_take_le _ _) (by decide)
 · decide

/-- Machine group at every caller-established source group index; child output
is derived here rather than required from the caller. -/
theorem chunk_group (digest : Array U8 32#usize) (chunk : Nat) (g : Usize)
 (_group_bound : g.val < 8) :
 ∃ word byte,
 PCG_PackLaw.readWord 0#u64 ((digest.val.drop (7*chunk)).take 7) = ok word ∧
 PCG_PackRef.group word g = ok byte ∧
 byte.val = PCG_PackLaw.word ((digest.val.drop (7*chunk)).take 7) /
  PCG_PackLaw.denominator g.val % 128 := by
 obtain ⟨word,hw,vw⟩ := chunk_word digest chunk
 obtain ⟨byte,hb,vb,_⟩ := PCG_PackLaw.group_step word g
 exact ⟨word,byte,hw,hb,by rw [vb,vw]⟩

theorem pack_at (digest : Array U8 32#usize) (chunk group : Nat)
 (bound : group < 8) :
 PCG_PackLaw.pack digest (8*chunk+group) =
 PCG_PackLaw.word ((digest.val.drop (7*chunk)).take 7) /
 PCG_PackLaw.denominator group % 128 := by
 have quotient : (8*chunk+group)/8 = chunk := by omega
 have remainder : (8*chunk+group)%8 = group := by omega
 simp only [PCG_PackLaw.pack,quotient,remainder]

/-- Complete 32-byte functional memory image after the nested source loops.
Native word/group/window certificates establish exactly the one-step updates;
chunk_word/chunk_group establish the machine/natural value association. -/
theorem row_293 (digest : Array U8 32#usize) :
 (fun index : Fin 32 => chunks digest 4 index.val) =
 (fun index : Fin 32 => PCG_PackLaw.pack digest index.val) ∧
 ∀ index : Fin 32, chunks digest 4 index.val < 128 := by
 constructor
 · funext index
   have h : index.val < 8*4 := by have hi := index.isLt; omega
   rw [chunk_induction,if_pos h]
 · intro index
   have h : index.val < 8*4 := by have hi := index.isLt; omega
   rw [chunk_induction,if_pos h]
   exact (PCG_PackLaw.row_293 digest index.val index.isLt).1

#print axioms writeRange_exact
#print axioms chunk_induction
#print axioms chunk_word
#print axioms chunk_group
#print axioms pack_at
#print axioms row_293
end PCG_PackComposition
