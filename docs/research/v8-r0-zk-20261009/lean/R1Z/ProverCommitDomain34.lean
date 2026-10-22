import R1Z.ProverCommitPublicRawBridge34
import R1Z.ProverCommitPublicImage33
/-! D146's announced domain, using the actual extracted serializer carrier.
`sourceImage` preserves every R0P.Public field; metadata omitted by the shipped
serializer is not silently hashed. No nonzero withdrawal condition is added.
This is an extracted-source/P6 statement, not an allocator or OS law. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitDomain34
open R1Z.PrivacyR1AcctBasis
open AspisR1 AspisR1PublicSerializer

abbrev Source := Whole431.Public
abbrev SourceBytes := FieldsRefinement431.ByteVec

def liftWord (w : PublicRawCore.Word) : K :=
  algebraMap (ZMod AspisCircleGroupOrder.P) K (w.val : ZMod AspisCircleGroupOrder.P)

def lowerWord (w : K) : PublicRawCore.Word :=
  ⟨w.re.re.re.val, by
    have bound := w.re.re.re.val_lt
    norm_num [AspisCircleGroupOrder.P] at bound ⊢
    omega⟩

theorem lower_lift (w : PublicRawCore.Word) (hw : w.val < 2147483647) :
    lowerWord (liftWord w) = w := by
  apply Fin.ext
  simp only [lowerWord,liftWord,base_coordinates]
  change (w.val : ZMod AspisCircleGroupOrder.P).val = w.val
  rw [ZMod.val_natCast]
  exact Nat.mod_eq_of_lt hw

def commonImage (c : PublicRawCore.Common) : R0P.Public K :=
  { variant := .privateTransfer
    anchor := fun i => liftWord (c.anchor i)
    nullifier := fun i => liftWord (c.nullifier i)
    assetId := liftWord c.assetId
    recipient := none
    change := fun i => liftWord (c.change i)
    withdrawalAmount := none
    nextPairIndex := c.nextPairIndex.val
    snapshotFrontier := fun l i => liftWord (c.snapshotFrontier l i)
    nextRoot := fun i => liftWord (c.nextRoot i)
    nextFrontier := fun l i => liftWord (c.nextFrontier l i) }

def image : PublicRawCore.Public → R0P.Public K
  | .transfer c recipient => {commonImage c with
      recipient := some (fun i => liftWord (recipient i))}
  | .withdrawal c amount => {commonImage c with
      variant := .withdrawal
      withdrawalAmount := some (liftWord amount)}

def lowerCommon (p : R0P.Public K) : PublicRawCore.Common :=
  { anchor := fun i => lowerWord (p.anchor i)
    nullifier := fun i => lowerWord (p.nullifier i)
    assetId := lowerWord p.assetId
    change := fun i => lowerWord (p.change i)
    nextPairIndex := ⟨p.nextPairIndex % 2^64, Nat.mod_lt _ (Nat.two_pow_pos 64)⟩
    snapshotFrontier := fun l i => lowerWord (p.snapshotFrontier l i)
    nextRoot := fun i => lowerWord (p.nextRoot i)
    nextFrontier := fun l i => lowerWord (p.nextFrontier l i) }

def lower (p : R0P.Public K) : PublicRawCore.Public :=
  match p.variant with
  | .privateTransfer => .transfer (lowerCommon p)
      (fun i => lowerWord ((p.recipient.getD (fun _ => 0)) i))
  | .withdrawal => .withdrawal (lowerCommon p) (lowerWord (p.withdrawalAmount.getD 0))

def commonCanonical (c : PublicRawCore.Common) : Prop :=
  (∀ i, (c.anchor i).val < 2147483647) ∧
  (∀ i, (c.nullifier i).val < 2147483647) ∧ c.assetId.val < 2147483647 ∧
  (∀ i, (c.change i).val < 2147483647) ∧
  (∀ l i, (c.snapshotFrontier l i).val < 2147483647) ∧
  (∀ i, (c.nextRoot i).val < 2147483647) ∧
  (∀ l i, (c.nextFrontier l i).val < 2147483647)

theorem canonical_transfer (c : PublicRawCore.Common) (r : PublicRawCore.Digest)
    (hc : PublicRawCore.Canonical (.transfer c r)) :
    commonCanonical c ∧ ∀ i, (r i).val < 2147483647 := by
  refine ⟨⟨?_,?_,?_,?_,?_,?_,?_⟩,?_⟩ <;> intros <;> apply hc <;>
    simp only [PublicRawCore.words,PublicRawCore.headerWords,PublicRawCore.afterWords,
      PublicRawCore.digestWords,PublicRawCore.frontierWords,List.mem_append,
      List.mem_cons,List.mem_nil_iff,List.mem_ofFn,List.mem_flatMap] <;> aesop

theorem canonical_withdrawal (c : PublicRawCore.Common) (a : PublicRawCore.Word)
    (hc : PublicRawCore.Canonical (.withdrawal c a)) :
    commonCanonical c ∧ a.val < 2147483647 := by
  refine ⟨⟨?_,?_,?_,?_,?_,?_,?_⟩,?_⟩ <;> intros <;> apply hc <;>
    simp only [PublicRawCore.words,PublicRawCore.headerWords,PublicRawCore.afterWords,
      PublicRawCore.digestWords,PublicRawCore.frontierWords,List.mem_append,
      List.mem_cons,List.mem_nil_iff,List.mem_ofFn,List.mem_flatMap] <;> aesop

theorem lower_common (c : PublicRawCore.Common) (hc : commonCanonical c) :
    lowerCommon (commonImage c) = c := by
  rcases hc with ⟨ha,hn,hi,hc,hs,hr,hf⟩
  have index : (⟨c.nextPairIndex.val % 2^64, Nat.mod_lt _ (Nat.two_pow_pos 64)⟩ : PublicRawCore.Index) =
      c.nextPairIndex := Fin.ext (Nat.mod_eq_of_lt c.nextPairIndex.isLt)
  simp only [lowerCommon,commonImage, lower_lift _ (ha _),lower_lift _ (hn _),
    lower_lift _ hi,lower_lift _ (hc _),lower_lift _ (hs _ _),lower_lift _ (hr _),
    lower_lift _ (hf _ _),index]

theorem lower_image (p : PublicRawCore.Public) (hc : PublicRawCore.Canonical p) : lower (image p) = p := by
  cases p with
  | transfer c r =>
    obtain ⟨hcommon,hr⟩ := canonical_transfer c r hc
    have h := lower_common c hcommon
    simpa only [lower,image,commonImage,lowerCommon,Option.getD_some,
      lower_lift _ (hr _)] using congrArg (fun c => PublicRawCore.Public.transfer c r) h
  | withdrawal c a =>
    obtain ⟨hcommon,ha⟩ := canonical_withdrawal c a hc
    have h := lower_common c hcommon
    simpa only [lower,image,commonImage,lowerCommon,Option.getD_some,
      lower_lift _ ha] using congrArg (fun c => PublicRawCore.Public.withdrawal c a) h

/-- Fixed semantic field projection of the extracted shipped source record. -/
def sourceImage (p : Source) : R0P.Public K := image (RawBridge431.project p)

/-- Announced statement-domain restriction. The commitment component is not
restricted here, and the adversary and its queries remain arbitrary. -/
def DeployedStatement (x : R0P.Public K) : Prop :=
  ∃ (p : Source) (out : SourceBytes), sourceImage p = x ∧
    pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes p = Aeneas.Std.Result.ok (.Ok out)

/-- Fixed byte function of the model statement; no chosen source witness. -/
def pubBytes (x : R0P.Public K) : PublicRawCore.Bytes := PublicRawCore.encode (lower x)

theorem source_bytes (p : Source) (out : SourceBytes)
    (hs : pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes p =
      Aeneas.Std.Result.ok (.Ok out)) :
    out.val.map RawBridge431.rawByte = pubBytes (sourceImage p) := by
  have h := RawBridge431.source_success_raw p out hs
  unfold PublicRawCore.serialize at h
  split at h
  next hc =>
    have hb := Option.some.inj h
    rw [pubBytes,sourceImage,lower_image _ hc]
    exact hb.symm
  next hc => contradiction

/-- Any successful representative has exactly the public bytes of its model
statement, so witness choice cannot change the public transcript. -/
theorem on_domain (x : R0P.Public K) (hx : DeployedStatement x) :
    ∃ (p : Source) (out : SourceBytes), sourceImage p = x ∧
      pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes p =
        Aeneas.Std.Result.ok (.Ok out) ∧ out.val.map RawBridge431.rawByte = pubBytes x := by
  obtain ⟨p,out,rfl,hs⟩ := hx
  exact ⟨p,out,rfl,hs,source_bytes p out hs⟩

def sourceByte (b : PublicRawCore.Byte) : Aeneas.Std.U8 :=
  Aeneas.Std.UScalar.mk (BitVec.ofFin b)

theorem sourceByte_rawByte (b : Aeneas.Std.U8) : sourceByte (RawBridge431.rawByte b) = b := by
  apply Aeneas.Std.UScalar.eq_of_val_eq
  rfl

theorem encodeWords_length (ws : List PublicRawCore.Word) :
    (PublicRawCore.encodeWords ws).length = 4 * ws.length := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp only [PublicRawCore.encodeWords,List.flatMap_cons,
      List.length_append,PublicRawCore.wordBytes,List.length_ofFn] at *
    rw [ih]
    simp only [List.length_cons]
    omega

theorem encoded_length_bound (p : PublicRawCore.Public) :
    (PublicRawCore.encode p).length ≤ 1455 := by
  have flatlen {α β : Type} (xs : List α) (f : α → List β) (n : Nat)
      (hf : ∀ x, (f x).length = n) : (xs.flatMap f).length = n * xs.length := by
    induction xs with
    | nil => simp only [List.flatMap_nil,List.length_nil,Nat.mul_zero]
    | cons x xs ih =>
      simp only [List.flatMap_cons,List.length_append,hf,ih,List.length_cons]
      simp only [Nat.mul_add,Nat.mul_one]
      omega
  have frontier (f : PublicRawCore.Frontier) :
      (PublicRawCore.frontierWords f).length = 160 := by
    unfold PublicRawCore.frontierWords
    rw [flatlen (List.ofFn f) PublicRawCore.digestWords 8 (fun _ => List.length_ofFn)]
    rw [List.length_ofFn]
  cases p <;> simp only [PublicRawCore.encode,PublicRawCore.afterBytes,
    encodeWords_length,PublicRawCore.headerWords,PublicRawCore.digestWords,
    PublicRawCore.afterWords,frontier,PublicRawCore.indexBytes,List.length_ofFn,
    List.length_append,List.length_cons,List.length_nil] <;> omega

/-- Source-sized canonical byte vector, with no error sentinel or admission
condition. Only its use on DeployedStatement is part of the deployed claim. -/
def sourcePubBytes (x : R0P.Public K) : SourceBytes :=
  ⟨(pubBytes x).map sourceByte, by
    have bound := encoded_length_bound (lower x)
    change ((PublicRawCore.encode (lower x)).map sourceByte).length ≤ _
    simp only [List.length_map]
    exact le_trans bound (by scalar_tac)⟩

theorem source_bytes_exact (p : Source) (out : SourceBytes)
    (hs : pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes p =
      Aeneas.Std.Result.ok (.Ok out)) : out = sourcePubBytes (sourceImage p) := by
  apply Subtype.ext
  change out.val = (pubBytes (sourceImage p)).map sourceByte
  rw [← source_bytes p out hs,List.map_map]
  simp only [Function.comp_def,sourceByte_rawByte]
  exact (List.map_id out.val).symm

theorem public_bytes_ok (x : R0P.Public K) (hx : DeployedStatement x) :
    ∃ p : Source, sourceImage p = x ∧
      pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes p =
        Aeneas.Std.Result.ok (.Ok (sourcePubBytes x)) := by
  obtain ⟨p,out,rfl,hs⟩ := hx
  exact ⟨p,rfl,by rw [← source_bytes_exact p out hs]; exact hs⟩


/-- Outside the domain, no source representative can return any proof-input
public bytes. This does not invent an API accepting arbitrary wide records. -/
theorem outside_no_serializer_success (x : R0P.Public K) (hx : ¬ DeployedStatement x)
    (p : Source) (hp : sourceImage p = x) (out : SourceBytes) :
    pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes p ≠
      Aeneas.Std.Result.ok (.Ok out) := by
  intro hs
  exact hx ⟨p,out,hp,hs⟩

#print axioms lower_lift
#print axioms canonical_transfer
#print axioms canonical_withdrawal
#print axioms lower_common
#print axioms lower_image
#print axioms source_bytes
#print axioms on_domain
#print axioms sourceByte_rawByte
#print axioms encodeWords_length
#print axioms encoded_length_bound
#print axioms source_bytes_exact
#print axioms public_bytes_ok
#print axioms outside_no_serializer_success
end R1Z.ProverCommitDomain34
