import R1Z.PhaseProtocolInstanceBin

/-! Byte lengths and typed coverage of the constructed protocol, independent
of Rust execution joins. All facts hold on arbitrary counterfactual views. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PhaseProtocolCoverageBin
open R0P R0Z R0Z.JointView R0Z.FsStatement R1Z.Batched R1Z.GamesR1
  R1Z.GamesR1PBin R1Z.TranscriptR1 R1Z.LensR1 R1Z.PhaseMessageEncodingBin
  R1Z.PhaseProtocolInstanceBin
local notation "K" => AspisWideTower.WideExact

/-- Count a fixed-width vector symbolically, without evaluating its cells. -/
theorem flatten_length {n m : ℕ} (xs : Fin n → List UInt8)
    (hf : ∀ i, (xs i).length = m) :
    (List.ofFn xs).flatten.length = n * m := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, List.flatten_cons, List.length_append, hf 0,
      ih (fun i => xs i.succ) (fun i => hf i.succ)]
    rw [Nat.succ_mul]
    omega

theorem wide_length (a : K) : (wideBytes a).length = 32 := by
  simpa only [wideBytes, List.length_map] using
    AspisR1.FoldedLeafCodec.encodeWide_length a

theorem encoded_length {n : ℕ} (xs : Fin n → K) :
    (encoded wideBytes xs).length = n * 32 := by
  unfold encoded AspisR1.FixedWidthDecoder.encode
  simpa only [List.flatMap_def, List.map_ofFn, Function.comp_def] using
    (flatten_length (fun i => wideBytes (xs i)) (fun i => wide_length (xs i)))

theorem semantic_length (p : R0Z.HonestView.Payload K R1Bat)
    (root : OracleAnswer) (i : Fin 27) :
    (semantic wideBytes p root i).length = WireLengthsR1PBin.semanticSize i := by
  unfold semantic WireLengthsR1PBin.semanticSize
  split_ifs
  all_goals try simp only [length_ans, wide_length, encoded_length, List.length_append,
    flatten_length _ (fun _ => encoded_length _), List.length_nil]
  all_goals omega

theorem opening_length (p : R0Z.HonestView.Payload K R1Bat)
    (root : OracleAnswer) (i : Fin 4) :
    (opening wideBytes p root i).length = WireLengthsR1PBin.openingSize i := by
  unfold opening WireLengthsR1PBin.openingSize
  split <;> (try split) <;> (try split)
  all_goals try simp only [length_ans, wide_length, encoded_length, List.length_append]

theorem final_length {CommitHandle Aux : Type}
    (v : ZkStatement.View K CommitHandle Aux R1Bat) :
    (PhaseMessageEncodingBin.final wideBytes v).length = 2048 := encoded_length _

/-- The first 26 lanes are four bytes and the last is sixteen bytes. -/
theorem c1_slot_length (xs : Fin 27 → K) :
    (List.ofFn (fun c : Fin 27 => (wideBytes (xs c)).take
      (if c.val < 26 then 4 else 16))).flatten.length = 120 := by
  rw [List.ofFn_succ', List.concat_eq_append, List.flatten_append,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.length_append]
  have hl : ∀ c : Fin 26, ((wideBytes (xs c.castSucc)).take
      (if c.castSucc.val < 26 then 4 else 16)).length = 4 := by
    intro c
    simp only [Fin.val_castSucc]
    rw [if_pos c.isLt, List.length_take, wide_length]
    rfl
  rw [flatten_length _ hl]
  simp only [Fin.val_last, Nat.lt_irrefl, if_false, List.length_take, wide_length]
  rfl


theorem c1_length (m : Fin 27 → Fin 1024 → K) (u : Fib) :
    (PhaseLeafEncodingBin.encoding.c1 m u).length = 480 := by
  unfold PhaseLeafEncodingBin.encoding
  exact flatten_length _ (fun _ => c1_slot_length _)

theorem c2_length (m : Fin 2 → Fin 1024 → K) (u : Fib) :
    (PhaseLeafEncodingBin.encoding.c2 m u).length = 128 := by
  unfold PhaseLeafEncodingBin.encoding
  dsimp only
  apply flatten_length (m := 32)
  intro s
  apply flatten_length (m := 16)
  intro c
  rw [List.length_take, wide_length]
  rfl

theorem folded_length (m : Fin 256 → K) (u : Fib) :
    (PhaseLeafEncodingBin.encoding.folded m u).length = 128 := by
  unfold PhaseLeafEncodingBin.encoding PhaseLeafEncodingBin.foldedLeaf
  dsimp only
  split <;> simp only [List.length_map, AspisR1.FoldedLeafCodec.encodeFolded_length,
    List.length_replicate]

theorem leaf_length {CommitHandle : Type} {F : Subfield K}
    (B : PackBasis F) (h : HonestProver K) (w : h.Instance)
    (x : Statement K CommitHandle) (τ : Tape K F) (ch : Challenges K) (T : Fin 3) (u : Fib) :
    (PhaseLeafConstructionBin.leafVal PhaseLeafEncodingBin.encoding B h w x τ ch T u).length =
      if T.val = 0 then 480 else 128 := by
  unfold PhaseLeafConstructionBin.leafVal
  split <;> (try split) <;> simp only [c1_length, c2_length, folded_length]

theorem byte_mod_eq (n : ℕ) :
    UInt8.ofFin ⟨n % 256, Nat.mod_lt _ (by decide)⟩ = (n % 256).toUInt8 := by
  apply UInt8.toNat_inj.mp
  change n % 256 = (n % 256) % 256
  exact (Nat.mod_mod n 256).symm

/-- Byte-carrier transport preserves the existing four little-endian bytes. -/
theorem length_bytes_eq (n : ℕ) :
    (AspisR1.PublicInitFrame.lengthBytes n).map UInt8.ofFin = le32 n := by
  simp only [AspisR1.PublicInitFrame.lengthBytes, List.ofFn_succ, List.ofFn_zero,
    List.map_cons, List.map_nil, le32, Fin.val_zero, Fin.val_succ]
  norm_num only [pow_zero, pow_one, Nat.div_one, Nat.reducePow]
  simp only [byte_mod_eq]

theorem framed_eq (tag : UInt8) (bs : List UInt8) :
    PhaseMessageEncodingBin.framed tag bs = [tag] ++ le32 bs.length ++ bs := by
  unfold PhaseMessageEncodingBin.framed AspisR1.RecordFrameCodec.frame
    AspisR1.RecordFrameCodec.header
  simp only [List.length_map, List.map_append, List.map_cons, List.map_nil,
    UInt8.ofFin_toFin, length_bytes_eq, List.map_map, Function.comp_def]
  congr 1
  exact List.map_id bs

/-- A list already proved to have the required width inhabits the typed carrier. -/
def bytesVector {n : ℕ} (bs : List UInt8) (hl : bs.length = n) : Vector UInt8 n :=
  ⟨bs.toArray, by simpa only [List.size_toArray] using hl⟩

theorem bytesVector_list {n : ℕ} (bs : List UInt8) (hl : bs.length = n) :
    (bytesVector bs hl).toList = bs := by
  simp only [bytesVector, Vector.toList, List.toList_toArray]

variable {CommitHandle Aux : Type} {F : Subfield K}

/-- The entire selected transcript is a D79/D81 wire, even off successful runs. -/
def transcriptWire (pub : List UInt8) (tag : UInt8)
    (v : ZkStatement.View K CommitHandle Aux R1Bat) (c2 cf : OracleAnswer) :
    WireLengthsR1PBin.Wire where
  semantic := fun i => bytesVector (semantic wideBytes v.2 c2 i) (semantic_length _ _ i)
  opening := fun i => bytesVector (opening wideBytes v.2 cf i) (opening_length _ _ i)
  final := bytesVector (PhaseMessageEncodingBin.final wideBytes v) (final_length v)
  publicBytes := pub
  tag := tag

theorem transcript_rest (base : R1Wire K CommitHandle Aux) (publicWidth : ℕ)
    (h : HonestProver K) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (x : Statement K CommitHandle) (v : ZkStatement.View K CommitHandle Aux R1Bat)
    (tr : TRead → OracleAnswer) (roots : Fin 3 → OracleAnswer) :
    (recP (wire base publicWidth h B outputs x).toWire x v tr roots).rest =
      WireLengthsR1PBin.rest (transcriptWire (base.pubBytes x) base.vtag v (roots 1) (roots 2)) := by
  change Rest.mk _ _ _ _ _ = Rest.mk _ _ _ _ _
  congr 1
  · funext i
    change PhaseMessageEncodingBin.framed _ _ = WireLengthsR1PBin.framed _ i
    rw [framed_eq]
    simp only [WireLengthsR1PBin.framed, transcriptWire, bytesVector_list, semantic_length]

/-- D84 coverage is a model theorem after the public byte width is chosen. -/
theorem read_coverage (base : R1Wire K CommitHandle Aux) (publicWidth : ℕ)
    (h : HonestProver K) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (x : Statement K CommitHandle)
    (seed : R1ProverP K CommitHandle Aux F (wire base publicWidth h B outputs x).toWire)
    (hp : (base.pubBytes x).length ≤ publicWidth) :
    RomGrammarBin.ReadCoverage (wire base publicWidth h B outputs x).toWire
      (prover base publicWidth h B outputs x seed).toProver publicWidth h B outputs x := by
  refine ⟨hp, ?_⟩
  intro w sec d v p
  cases p with
  | inl j =>
    let record := recP (wire base publicWidth h B outputs x).toWire x
      (view h B outputs x w
        (chOf (wire base publicWidth h B outputs x).toWire (trOf v))
        (tapeR (wire base publicWidth h B outputs x).toWire
          (prover base publicWidth h B outputs x seed).toProver v)) (trOf v) (rootsOf v)
    let tw := transcriptWire (base.pubBytes x) base.vtag
      (view h B outputs x w
        (chOf (wire base publicWidth h B outputs x).toWire (trOf v))
        (tapeR (wire base publicWidth h B outputs x).toWire
          (prover base publicWidth h B outputs x seed).toProver v))
      (rootsOf v 1) (rootsOf v 2)
    refine ⟨.transcript (SharedGrammarBridgeBin.toShared tw) hp j (fieldVal (fc j) record), ?_⟩
    change addrWith j (fieldVal (fc j) record)
      (WireLengthsR1PBin.rest (SharedGrammarBridgeBin.fromShared (SharedGrammarBridgeBin.toShared tw))) =
      addr j record
    rw [SharedGrammarBridgeBin.wire_roundtrip]
    unfold addr
    rw [show record.rest = WireLengthsR1PBin.rest tw from transcript_rest _ _ _ _ _ _ _ _ _]
  | inr c =>
    have hl : ∀ T u,
        ((prover base publicWidth h B outputs x seed).toProver.leafVal h w x
          (tapeR (wire base publicWidth h B outputs x).toWire
            (prover base publicWidth h B outputs x seed).toProver v)
          (chOf (wire base publicWidth h B outputs x).toWire (trOf v)) T u).length ≤ 480 := by
      intro T u
      change (PhaseLeafConstructionBin.leafVal PhaseLeafEncodingBin.encoding B h w x _ _ T u).length ≤ 480
      rw [leaf_length]
      split <;> omega
    exact ⟨.commitment (base.pubBytes x) hp base.vtag _ hl sec d (restOf v) c, rfl⟩

#print axioms flatten_length
#print axioms wide_length
#print axioms encoded_length
#print axioms semantic_length
#print axioms opening_length
#print axioms final_length
#print axioms c1_slot_length
#print axioms c1_length
#print axioms c2_length
#print axioms folded_length
#print axioms leaf_length
#print axioms byte_mod_eq
#print axioms length_bytes_eq
#print axioms framed_eq
#print axioms bytesVector_list
#print axioms transcript_rest
#print axioms read_coverage
end R1Z.PhaseProtocolCoverageBin
