import R0Z.BuilderModelHash
import R0P.Semantics

/-! Symbolic identification of the builder's block endpoints with the spend
semantics. No concrete permutation or recurrence is evaluated. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.BuilderSemanticBridge
open R0P R0Z.BuilderModel
variable {K : Type} [Field K]
attribute [local irreducible] poseidonPermutation blockIter layout cellsOf

/-- A block endpoint is the canonical permutation of the absorbed input. -/
theorem blockOut_endpoint (pub : Public K) (w : ModelWitness K) (b : BlockIn K) :
    blockOut b = poseidonPermutation
      (fun lane => if lane.val < 8 then b.pre lane + b.absorb lane else b.pre lane) := by
  let C : Cells K := { cellsOf pub w with blocks := fun _ => b }
  have h := poseidon_scalar_holds_output pub (layout C) (poseidon_layout pub C) 0
  have h0 : poseidonState (layout C) 0 0 = b.pre := by
    rw [state_layout]
    exact funext (fun lane => blockCell_pre b lane)
  have h12 : poseidonState (layout C) 0 12 = b.absorb := by
    rw [state_layout]
    exact blockCell_fun_absorb b
  have hi : poseidonAbsorbedInput (layout C) 0 =
      (fun lane => if lane.val < 8 then b.pre lane + b.absorb lane else b.pre lane) := by
    change (fun lane => if lane.val < 8 then
      poseidonState (layout C) 0 0 lane + poseidonState (layout C) 0 12 lane
      else poseidonState (layout C) 0 0 lane) = _
    rw [h0, h12]
  rw [state_layout] at h
  have h11 : ((11 : Fin 16) : Nat) = 11 := rfl
  rw [h11] at h
  rw [blockCell_fun_iter _ 11 (by omega), hi] at h
  exact h

/-- Model and spend semantics use the same sponge initial state. -/
theorem spongeInit_eq (dom len : K) :
    R0Z.BuilderModel.spongeInit dom len = R0P.spongeInit dom len := by
  funext l
  have e8 : ((8 : Fin 16) : Nat) = 8 := rfl
  have e9 : ((9 : Fin 16) : Nat) = 9 := rfl
  simp only [R0Z.BuilderModel.spongeInit, R0P.spongeInit, Fin.ext_iff, e8, e9]

/-- A rate-eight chunk in a model block is one semantic sponge step. -/
theorem blockOut_sponge (pub : Public K) (w : ModelWitness K)
    (pre : Fin 16 → K) (chunk : Digest K) :
    blockOut ⟨pre, lo8 chunk⟩ = spongeStep pre chunk := by
  rw [blockOut_endpoint pub w]
  unfold spongeStep absorb
  congr 1
  funext l
  by_cases hl : l.val < 8 <;> simp [hl, lo8]

/-- The owner-key endpoint is the spend relation's owner hash. -/
theorem ownerDigest_eq (pub : Public K) (w : ModelWitness K) :
    ownerDigest w = ownerKey w.sk := by
  unfold ownerDigest ownerB blockDigest ownerKey digestOf
  rw [blockOut_sponge pub w, spongeInit_eq]
  rfl

/-- The nullifier endpoint uses the same two sponge chunks. -/
theorem nullifierDigest_eq (pub : Public K) (w : ModelWitness K) :
    nullifierDigest w = nullifierHash w.sk w.salt := by
  unfold nullifierDigest nulB1 nulB0 blockDigest nullifierHash digestOf
  rw [blockOut_sponge pub w, blockOut_sponge pub w, spongeInit_eq]
  rfl

/-- The model's second note chunk, embedded at rate eight. -/
theorem noteC2_eq (value asset : K) (salt : Digest K) :
    noteC2 value asset salt = lo8 (fun i : Fin 8 =>
      if i.val = 0 then value else if i.val = 1 then asset
      else salt ⟨i.val - 2, by omega⟩) := by
  funext l
  fin_cases l <;> simp [noteC2, lo8]

/-- The final note chunk contains just the remaining two salt limbs. -/
theorem noteC3_eq (salt : Digest K) :
    noteC3 salt = lo8 (fun i : Fin 8 =>
      if h : i.val < 2 then salt ⟨i.val + 6, by omega⟩ else 0) := by
  funext l
  fin_cases l <;> simp [noteC3, lo8]

/-- All three note blocks implement the semantic note commitment. -/
theorem noteDigest_eq (pub : Public K) (w : ModelWitness K)
    (owner : Digest K) (value asset : K) (salt : Digest K) :
    noteDigest owner value asset salt = noteCommitment owner value asset salt := by
  unfold noteDigest noteB2 noteB1 noteB0 blockDigest noteCommitment digestOf
  rw [noteC3_eq, blockOut_sponge pub w, noteC2_eq,
    blockOut_sponge pub w, blockOut_sponge pub w, spongeInit_eq]
  rfl

/-- The input commitment's owner is the hash of the secret key. -/
theorem inputLeaf_eq (pub : Public K) (w : ModelWitness K) :
    inputLeaf pub w = noteCommitment (ownerKey w.sk)
      (w.inputValue.val : K) pub.assetId w.salt := by
  unfold inputLeaf
  rw [noteDigest_eq pub w, ownerDigest_eq pub w]

/-- The change endpoint is the semantic change commitment. -/
theorem changeDigest_eq (pub : Public K) (w : ModelWitness K) :
    changeDigest pub w = noteCommitment w.changeOwner
      (w.changeValue.val : K) pub.assetId w.changeSalt := by
  exact noteDigest_eq pub w _ _ _ _

/-- The transfer recipient endpoint is the semantic recipient commitment. -/
theorem recipientDigest_eq (pub : Public K) (w : ModelWitness K)
    (hv : pub.variant = .privateTransfer) :
    recipientDigest pub w = noteCommitment w.recipientOwner
      (w.outputValue.val : K) pub.assetId w.recipientSalt := by
  unfold recipientDigest recipB
  rw [hv]
  exact noteDigest_eq pub w _ _ _ _

/-- The node tweak uses addition in the writer and subtraction in R0P. -/
theorem nodeDigest_eq [CharP K 2147483647] (pub : Public K) (w : ModelWitness K)
    (left right : Digest K) : blockDigest (nodeIn left right) = nodeCompress left right := by
  have hp : (2147483647 : K) = 0 := CharP.cast_eq_zero K 2147483647
  have ht : (0x41531005 : K) = -(1051521018 : K) := by linear_combination hp
  unfold blockDigest nodeCompress digestOf
  rw [blockOut_endpoint pub w]
  apply congrArg (fun s : Fin 16 → K => fun i : Fin 8 => s (i.castAdd 8))
  congr 1
  funext l
  by_cases hl : l.val < 8
  · simp [nodeIn, lo8, hl]
  · simp [nodeIn, lo8, hl, ht, sub_eq_add_neg]

/-- Every membership prefix agrees, without evaluating the recurrence. -/
theorem treeCur_eq [CharP K 2147483647] (pub : Public K) (w : ModelWitness K)
    (leaf : Digest K) (n : Nat) : treeCur w leaf n = merkleRootAux leaf w.path n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [treeCur, merkleRootAux]
    split_ifs with hn
    · rw [treeNode, nodeDigest_eq pub w, ih]
      cases hb : (w.path ⟨n, hn⟩).1 <;> simp [ordered, merkleStep]
    · exact ih

#print axioms blockOut_endpoint
#print axioms spongeInit_eq
#print axioms blockOut_sponge
#print axioms ownerDigest_eq
#print axioms nullifierDigest_eq
#print axioms noteC2_eq
#print axioms noteC3_eq
#print axioms noteDigest_eq
#print axioms inputLeaf_eq
#print axioms changeDigest_eq
#print axioms recipientDigest_eq
#print axioms nodeDigest_eq
#print axioms treeCur_eq
end R1Z.BuilderSemanticBridge
