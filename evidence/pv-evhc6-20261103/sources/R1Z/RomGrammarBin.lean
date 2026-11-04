import R1Z.RomFiniteBin
import R1Z.SharedGrammarBridgeBin

/-! Membership of the actual binary encodings, including private-only reads
and D79 checkpoint classes. Coverage is the source handoff, at every answer
vector; it is not inferred from a successful trace or opening-only comLog. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.RomGrammarBin
open R0P R0Z R0Z.JointView R0Z.FsStatement
  R1Z.GamesR1 R1Z.TranscriptR1 R1Z.LensR1 R1Z.GamesR1PBin
  R1Z.LayoutR1PBin R1Z.CouplingR1PBin R1Z.RomFiniteBin
open AspisR1.WireBindingRecordCodec
attribute [local instance] Classical.propDecidable

/-- Room for all fixed records plus the public statement and init domains. -/
def bound (publicWidth : ℕ) : ℕ :=
  57607 + publicWidth + semDomain.length + openDomain.length

theorem class_size_le (c : Tx1Class) : c.size ≤ 57607 := by
  cases c <;> simp only [Tx1Class.size]
  all_goals first
    | omega
    | (rename_i k; cases k <;>
        simp only [BindingClass.size, proof_bytes_eq, asf8_size_eq] <;> omega)

theorem semantic_size_le (i : Fin 27) :
    AspisR1.SharedBinaryRecordGrammar.semanticSize i ≤ 3712 := by
  unfold AspisR1.SharedBinaryRecordGrammar.semanticSize
  split <;> (try split) <;> (try split) <;> (try split) <;> omega

theorem opening_size_le (i : Fin 4) :
    AspisR1.SharedBinaryRecordGrammar.openingSize i ≤ 928 := by
  unfold AspisR1.SharedBinaryRecordGrammar.openingSize
  split <;> (try split) <;> (try split) <;> omega

theorem transcript_length (publicWidth : ℕ)
    (w : AspisR1.SharedBinaryRecordGrammar.Wire) (hp : w.publicBytes.length ≤ publicWidth)
    (j : TRead) (a : OracleAnswer) :
    (addrWith j a (WireLengthsR1PBin.rest (SharedGrammarBridgeBin.fromShared w))).length ≤
      bound publicWidth := by
  have hs : ∀ i, WireLengthsR1PBin.semanticSize i ≤ 3712 := semantic_size_le
  have ho : ∀ i, WireLengthsR1PBin.openingSize i ≤ 928 := opening_size_le
  cases j <;>
    simp only [addrWith, List.length_append, List.length_cons, List.length_nil,
      length_ans, le32, WireLengthsR1PBin.rest,
      SharedGrammarBridgeBin.fromShared, WireLengthsR1PBin.framed,
      Vector.length_toList]
  all_goals unfold bound
  all_goals first
    | omega
    | (rename_i i; have hi := hs i; change _ ≤ _ at hi; omega)
    | (rename_i i; have hi := ho i; change _ ≤ _ at hi; omega)

theorem commitment_length {E₁ E₂ : ℕ} (publicWidth : ℕ)
    (pub : List UInt8) (hp : pub.length ≤ publicWidth) (tag : UInt8)
    (lv : Fin 3 → Fib → List UInt8) (hl : ∀ T u, (lv T u).length ≤ 480)
    (sec : SecP) (d : OracleAnswer) (rest : RIdx → OracleAnswer) (p : CPos E₁ E₂) :
    (gram pub tag lv sec d rest p).length ≤ bound publicWidth := by
  rcases p with T | ((c | c) | (b | (i | (⟨T,u⟩ | (⟨T,u⟩ | ⟨T,n⟩)))))
  all_goals simp only [gram]
  all_goals try split_ifs
  all_goals simp only [nodeBytes, ctxEnc, le32, le64, dExp1, dExp2, dBind0,
    dBind1, dMaskSeed, dSourceSeed, dDSeed, dLeafSalt, descr,
    List.length_append, List.length_cons, List.length_nil, length_ans]
  all_goals unfold bound
  all_goals first | omega | (have hv := hl T u; omega)

/-- Typed read carrier. Commitment records include roots, all internal
parents, all salted leaves, both bindings, every seed/salt/expander block.
The classified constructor additionally covers D79 checkpoint/resume sites. -/
inductive Record (publicWidth : ℕ) where
  | transcript (w : AspisR1.SharedBinaryRecordGrammar.Wire)
      (hp : w.publicBytes.length ≤ publicWidth) (j : TRead) (a : OracleAnswer)
  | commitment {E₁ E₂ : ℕ} (pub : List UInt8) (hp : pub.length ≤ publicWidth)
      (tag : UInt8) (lv : Fin 3 → Fib → List UInt8)
      (hl : ∀ T u, (lv T u).length ≤ 480) (sec : SecP) (d : OracleAnswer)
      (rest : RIdx → OracleAnswer) (p : CPos E₁ E₂)
  | classified (c : Tx1Class) (bs : Vector UInt8 c.size)
  | publicDigest (bs : List UInt8) (hp : bs.length ≤ publicWidth)

def Record.bytes {publicWidth : ℕ} : Record publicWidth → List UInt8
  | .transcript w _ j a =>
      addrWith j a (WireLengthsR1PBin.rest (SharedGrammarBridgeBin.fromShared w))
  | .commitment pub _ tag lv _ sec d rest p => gram pub tag lv sec d rest p
  | .classified _ bs => bs.toList
  | .publicDigest bs _ => bs

theorem record_length {publicWidth : ℕ} (r : Record publicWidth) :
    r.bytes.length ≤ bound publicWidth := by
  cases r with
  | transcript w hp j a => exact transcript_length publicWidth w hp j a
  | commitment pub hp tag lv hl sec d rest p =>
      exact commitment_length publicWidth pub hp tag lv hl sec d rest p
  | classified c bs =>
      simp only [Record.bytes, Vector.length_toList]
      have hc := class_size_le c
      unfold bound
      omega
  | publicDigest bs hp =>
      change bs.length ≤ bound publicWidth
      unfold bound
      omega

theorem record_in_domain {publicWidth : ℕ} (r : Record publicWidth) :
    (decode (bound publicWidth) r.bytes).isSome :=
  (decode_isSome _ _).mpr (record_length r)

variable {K CommitHandle Aux : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}

/-- R10/R-wire handoff. All counterfactual answers, not just successful runs.
The source inventory must separately identify any extra operational hashes;
no claim that Pos1 enumerates such additional source calls is made here. -/
structure ReadCoverage (W : R1Wire K CommitHandle Aux)
    (Pr : R1ProverP K CommitHandle Aux F W) (publicWidth : ℕ)
    (h : HonestProver K) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (x : Statement K CommitHandle) : Prop where
  public_bytes : (W.pubBytes x).length ≤ publicWidth
  reads : ∀ (w : h.Instance) (sec : SecP) (d : OracleAnswer)
    (v : Pos1 Pr.E₁ Pr.E₂ → OracleAnswer) (p : Pos1 Pr.E₁ Pr.E₂),
    ∃ r : Record publicWidth, r.bytes = attAddr W Pr h B outputs x w sec d v p

theorem address_domain (base : R1Wire K CommitHandle Aux) (publicWidth : ℕ)
    (Pr : R1ProverP K CommitHandle Aux F (wire base (bound publicWidth)))
    (h : HonestProver K) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (x : Statement K CommitHandle)
    (coverage : ReadCoverage (wire base (bound publicWidth)) Pr publicWidth h B outputs x)
    (w : h.Instance) :
    RAddrIn (wire base (bound publicWidth)) Pr (rom base (bound publicWidth)) h B outputs x w := by
  intro sec d v p
  obtain ⟨r, hr⟩ := coverage.reads w sec d v p
  change (decode (bound publicWidth) _).isSome
  rw [← hr]
  exact record_in_domain r

/-- The frozen statement-digest address is included as well. -/
theorem public_digest_domain (base : R1Wire K CommitHandle Aux) (publicWidth : ℕ)
    (Pr : R1ProverP K CommitHandle Aux F (wire base (bound publicWidth)))
    (h : HonestProver K) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (x : Statement K CommitHandle)
    (coverage : ReadCoverage (wire base (bound publicWidth)) Pr publicWidth h B outputs x) :
    ((rom base (bound publicWidth)).dec ((wire base (bound publicWidth)).pubBytes x)).isSome :=
  record_in_domain (.publicDigest _ coverage.public_bytes)

#print axioms class_size_le
#print axioms semantic_size_le
#print axioms opening_size_le
#print axioms transcript_length
#print axioms commitment_length
#print axioms record_length
#print axioms record_in_domain
#print axioms address_domain
#print axioms public_digest_domain
end R1Z.RomGrammarBin
