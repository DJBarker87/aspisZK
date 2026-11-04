import R1Z.LayoutR1PBin

/-! Binary-node separation. Commitment records have disjoint leading tags.
Duplex addresses begin with an arbitrary digest: their separation requires
record lengths, not a claim that every transcript address has a fixed tag. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.LayoutR1PBin
open R0Z.FsStatement R1Z.GamesR1PBin R1Z.TranscriptR1 R1Z.LensR1

variable {E₁ E₂ : ℕ}

def nodePosition : CPos E₁ E₂ → Prop
  | .inl _ => True
  | .inr (.inr (.inr (.inr (.inr (.inr _))))) => True
  | _ => False

theorem nodeBytes_length (rest : RIdx → OracleAnswer) (ch : Fin 2 → RIdx) :
    (nodeBytes rest ch).length = 65 := by simp [nodeBytes, length_ans]

theorem nodeBytes_ne_tag (rest : RIdx → OracleAnswer) (ch : Fin 2 → RIdx)
    (tag : UInt8) (tail : List UInt8) (ht : tag ≠ binTag) :
    nodeBytes rest ch ≠ tag :: tail := by
  intro h
  have hh := congrArg (fun l : List UInt8 => l[0]?) h
  simp [nodeBytes] at hh
  exact ht hh.symm

/-- All other commitment classes: bindings, seeds, salts, leaves, expanders. -/
theorem nodeBytes_ne_other_commit (rest₀ : RIdx → OracleAnswer) (ch : Fin 2 → RIdx)
    (pub : List UInt8) (vtag : UInt8) (lv : Fin 3 → Fib → List UInt8) (sec : SecP)
    (d : OracleAnswer) (rest : RIdx → OracleAnswer) (c : CPos E₁ E₂)
    (hn : ¬ nodePosition c) : nodeBytes rest₀ ch ≠ gram pub vtag lv sec d rest c := by
  rcases c with T | (c | c) | (b | i | ⟨T, u⟩ | ⟨T, u⟩ | ⟨T, n⟩)
  · exact False.elim (hn trivial)
  · exact nodeBytes_ne_tag _ _ _ _ (by decide)
  · exact nodeBytes_ne_tag _ _ _ _ (by decide)
  · by_cases hb : b.val = 0
    · simp only [gram, hb, if_true]
      exact nodeBytes_ne_tag _ _ _ _ (by decide)
    · simp only [gram, hb, if_false]
      exact nodeBytes_ne_tag _ _ _ _ (by decide)
  · by_cases h0 : i.val = 0
    · simp only [gram, h0, if_true]
      exact nodeBytes_ne_tag _ _ _ _ (by decide)
    · by_cases h1 : i.val = 1
      · simp only [gram, h1, if_true]
        exact nodeBytes_ne_tag _ _ _ _ (by decide)
      · simp only [gram, h0, h1, if_false]
        exact nodeBytes_ne_tag _ _ _ _ (by decide)
  · exact nodeBytes_ne_tag _ _ _ _ (by decide)
  · exact nodeBytes_ne_tag _ _ _ _ (by decide)
  · exact False.elim (hn trivial)

/-- Includes separation from the retained eight-way node format. -/
theorem nodeBytes_ne_eightway (rest : RIdx → OracleAnswer) (ch : Fin 2 → RIdx)
    (tail : List UInt8) : nodeBytes rest ch ≠ (0x18 : UInt8) :: tail :=
  nodeBytes_ne_tag _ _ _ _ (by decide)

/-- Avoid unfolding a byte-array traversal for each literal domain. -/
theorem byteArray_toList_length (bs : ByteArray) : bs.toList.length = bs.size := by
  have aux : ∀ n i acc, bs.size - i = n →
      (ByteArray.toList.loop bs i acc).length = acc.length + n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro i acc hn
      rw [ByteArray.toList.loop]
      split
      · rename_i hi
        rw [ih (bs.size - (i + 1)) (by omega) (i + 1) (bs.get! i :: acc) rfl]
        simp only [List.length_cons]
        omega
      · simp only [List.length_reverse]
        omega
  simpa only [ByteArray.toList, List.length_nil, Nat.zero_add] using
    (aux bs.size 0 [] (by omega))

/-- Named wire-length condition: `Rest` otherwise permits arbitrary bytes.
The wire/source refinement must establish this for actual message encodings. -/
def TranscriptNodeLengths (r : Rest) : Prop :=
  (∀ i, (r.framed i).length ≠ 31) ∧
  (∀ i, (r.payload i).length ≠ 27) ∧ r.final.length ≠ 27

theorem nodeBytes_ne_transcript (rest : RIdx → OracleAnswer) (ch : Fin 2 → RIdx)
    (j : TRead) (f : OracleAnswer) (r : Rest) (hr : TranscriptNodeLengths r) :
    nodeBytes rest ch ≠ addrWith j f r := by
  intro h
  have hl := congrArg List.length h
  rw [nodeBytes_length] at hl
  cases j with
  | init =>
      have hs : semDomain.length = 38 := by
        rw [semDomain, byteArray_toList_length]; rfl
      simp only [addrWith, List.length_append, List.length_singleton, length_ans] at hl
      simp only [le32, List.length_cons, List.length_nil] at hl
      rw [hs] at hl
      omega
  | reseed =>
      have hs : openDomain.length = 29 := by
        rw [openDomain, byteArray_toList_length]; rfl
      simp only [addrWith, List.length_append, List.length_singleton, length_ans] at hl
      rw [hs] at hl
      omega
  | absS i =>
      have hi := hr.1 i
      simp only [addrWith, List.length_append, length_ans, List.length_cons,
        List.length_nil] at hl
      omega
  | absO i =>
      have hi := hr.2.1 i
      simp [addrWith, length_ans, le32] at hl
      omega
  | absQ =>
      have hi := hr.2.2
      simp [addrWith, length_ans, le32] at hl
      omega
  | absR => simp [addrWith, length_ans, le32] at hl
  | sqS _ | advS _ | sqO _ | advO _ | qb _ | qa _ | sqR | advR =>
      simp [addrWith, length_ans] at hl

#print axioms byteArray_toList_length
#print axioms nodeBytes_length
#print axioms nodeBytes_ne_tag
#print axioms nodeBytes_ne_other_commit
#print axioms nodeBytes_ne_eightway
#print axioms nodeBytes_ne_transcript
end R1Z.LayoutR1PBin
