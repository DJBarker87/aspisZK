import NGO_CallerDomains
import NKR_DigestChildren
import NJE_WellFrozen
import LIBC_ExpandSemanticModel
import LIB_VClaims
import LIBB_NullifierBytes
set_option autoImplicit false
/-! NPP_ hand-written refinement inputs (Stream A, gate row 5, step 3; lead decisions on
NPP_SELECTIONS.md). Target not yet established.

Computable decision procedures for two inductive/structure predicates, each proved by an explicit
characterization. They are new instances only; no original definition is changed. The stage-A
tool finds them through instance search, and equalities with the classical instances follow by
`Subsingleton.elim` as for every other site.

* C1: `NGO_CallerDomains.Call row n off` (five constructors) ↔ an explicit disjunction.
* C2: `AspisR1.NKR_DigestChildren.Domain p` (a structure of digest-range facts) ↔ the conjunction
  of its fields, with the `Option` field read through `Option.toList`.

B2 inspection: the elaborated decidability site of `NJE_WellFrozen.emitted` is printed. -/

namespace NPP_Refine

/-- C1: the five call shapes, as a decidable disjunction. -/
theorem call_iff (r n o : Nat) : NGO_CallerDomains.Call r n o ↔
    ((r = 14 ∧ n = 1 ∧ o = 0) ∨ (15 ≤ r ∧ r ≤ 24 ∧ n = 28 ∧ o = 0) ∨
     (r = 25 ∧ n = 29 ∧ (o = 0 ∨ o = 29 ∨ o = 58 ∨ o = 87)) ∨ (r = 26 ∧ n = 29 ∧ o = 0)) := by
  constructor
  · intro h
    cases h with
    | initial => exact Or.inl ⟨rfl, rfl, rfl⟩
    | round row l hh => exact Or.inr (Or.inl ⟨l, hh, rfl, rfl⟩)
    | claims p live =>
      refine Or.inr (Or.inr (Or.inl ⟨rfl, rfl, ?_⟩))
      have : p = 0 ∨ p = 1 ∨ p = 2 := by omega
      rcases this with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
    | extra => exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, Or.inr (Or.inr (Or.inr rfl))⟩))
    | beforeZ1 => exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))
  · rintro (⟨rfl, rfl, rfl⟩ | ⟨h1, h2, rfl, rfl⟩ | ⟨rfl, rfl, h | h | h | h⟩ | ⟨rfl, rfl, rfl⟩)
    · exact .initial
    · exact .round _ h1 h2
    · subst h; exact .claims 0 (by omega)
    · subst h; exact .claims 1 (by omega)
    · subst h; exact .claims 2 (by omega)
    · subst h; exact .extra
    · exact .beforeZ1

instance decCall (r n o : Nat) : Decidable (NGO_CallerDomains.Call r n o) :=
  decidable_of_iff _ (call_iff r n o).symm

/-- C2: the digest range predicate on one 8-word digest. -/
instance decDc (d : AspisR1.NJX_DigestCohort.D) : Decidable (AspisR1.NJX_DigestCohort.dc d) := by
  unfold AspisR1.NJX_DigestCohort.dc; infer_instance

open AspisR1 in
theorem domain_iff (p : NKI_InitialPrefix.Public) : NKR_DigestChildren.Domain p ↔
    (NJX_DigestCohort.dc p.anchor ∧ NJX_DigestCohort.dc p.nullifier ∧
     (∀ d ∈ p.recipient.toList, NJX_DigestCohort.dc d) ∧ NJX_DigestCohort.dc p.change ∧
     (∀ d ∈ p.transition.live_snapshot.frontier.val, NJX_DigestCohort.dc d) ∧
     NJX_DigestCohort.dc p.transition.candidate_afterstate.next_root ∧
     (∀ d ∈ p.transition.candidate_afterstate.next_frontier.val, NJX_DigestCohort.dc d)) := by
  constructor
  · intro h
    refine ⟨h.anchor, h.nullifier, ?_, h.change, h.frontier, h.nextRoot, h.nextFrontier⟩
    intro d hd
    cases hr : p.recipient with
    | none => rw [hr] at hd; cases hd
    | some x =>
      rw [hr] at hd
      have : d = x := by simpa using hd
      subst this
      exact h.recipient d hr
  · rintro ⟨a, b, c, d, e, f, g⟩
    refine ⟨a, b, ?_, d, e, f, g⟩
    intro x hx
    exact c x (by rw [hx]; simp)

open AspisR1 in
instance decDomain (p : NKI_InitialPrefix.Public) : Decidable (NKR_DigestChildren.Domain p) :=
  decidable_of_iff _ (domain_iff p).symm

end NPP_Refine

/-! A1 (approved): `LIBC_ExpandSemanticModel.Row` selects the packet row whose output interval
contains `j`. The intervals are pairwise disjoint: adjacent rows abut by the existing per-row fact
`NGD_SemanticSchedule.advance` (`dst (r+1) = dst r + 5 + payloadSize r`), so `dst` is monotone and
two rows containing `j` coincide. The copy is the first match in `List.range 27`; its equation is
`Subtype.ext` plus that uniqueness. -/
namespace NPP_Refine
open NGD_SemanticSchedule NFU_PacketDomains

/-- the row predicate of `Row` -/
abbrev RowP (j r : Nat) : Prop := r < 27 ∧ dst r ≤ j ∧ j < dst r + 5 + payloadSize r

theorem dst_mono (a : Nat) : ∀ k, a + k ≤ 27 → dst a ≤ dst (a + k)
  | 0, _ => Nat.le_refl _
  | k + 1, h => by
    have ih := dst_mono a k (by omega)
    have step := (advance (a + k) (by omega)).2
    rw [← Nat.add_assoc, step]
    omega

theorem row_unique (j r1 r2 : Nat) (h1 : RowP j r1) (h2 : RowP j r2) : r1 = r2 := by
  rcases Nat.lt_trichotomy r1 r2 with h | h | h
  · exfalso
    have step := (advance r1 h1.1).2
    have m := dst_mono (r1 + 1) (r2 - (r1 + 1)) (by omega)
    rw [show r1 + 1 + (r2 - (r1 + 1)) = r2 by omega] at m
    omega
  · exact h
  · exfalso
    have step := (advance r2 h2.1).2
    have m := dst_mono (r2 + 1) (r1 - (r2 + 1)) (by omega)
    rw [show r2 + 1 + (r1 - (r2 + 1)) = r1 by omega] at m
    omega
end NPP_Refine

namespace NPP_C.LIBC_ExpandSemanticModel
open NGD_SemanticSchedule NFU_PacketDomains

/-- computable copy of `LIBC_ExpandSemanticModel.Row`: the first row of `List.range 27` whose
interval contains `j` -/
def Row (j : Fin 13831) (late : ¬ j.val < 32) :
    {r : Nat // r < 27 ∧ dst r ≤ j.val ∧ j.val < dst r + 5 + payloadSize r} :=
  match h : (List.range 27).find? (fun r => decide (NPP_Refine.RowP j.val r)) with
  | some r => ⟨r, by
      have hs := List.find?_some h
      exact of_decide_eq_true hs⟩
  | none => False.elim (by
      obtain ⟨r, hr⟩ := (NGV_SemanticPacket.coverage j.val j.isLt).resolve_left late
      have hn := List.find?_eq_none.mp h r (List.mem_range.mpr hr.1)
      exact hn (decide_eq_true hr))

theorem Row.npp_eq : @Row = @_root_.LIBC_ExpandSemanticModel.Row := by
  funext j late
  apply Subtype.ext
  exact NPP_Refine.row_unique j.val _ _ (Row j late).property (_root_.LIBC_ExpandSemanticModel.Row j late).property
end NPP_C.LIBC_ExpandSemanticModel

/-! B2 (decided by inspection NPP_L050: `reject : Prop`, bound from `ok True` or
`ok (len > 16)`). The copy binds the same two values as Booleans (`decide`); every
instantiation is concrete, and `npp_eq` is proved by cases on the first call's result. -/
namespace NPP_C.NJE_WellFrozen
open Aeneas Aeneas.Std Result NJA_Multiproof _root_.NJE_WellFrozen

def emitted (indices : Slice U32) : Result Bool := do
 let empty ← core.slice.Slice.is_empty indices
 let reject ← if empty then ok true else ok (decide (Slice.len indices > 16#usize))
 if reject then ok false else
 let ordered ← allCalls orderFn (NJA_WellIteration.windows indices.val)
 if ordered then allCalls domainFn indices.val else ok false

theorem emitted.npp_eq : @emitted = @_root_.NJE_WellFrozen.emitted := by
  funext indices
  unfold emitted _root_.NJE_WellFrozen.emitted
  cases core.slice.Slice.is_empty indices with
  | ok b =>
    cases b
    · by_cases h : Slice.len indices > 16#usize <;> simp [h]
    · simp
  | fail e => rfl
  | div => rfl
end NPP_C.NJE_WellFrozen

/-! E (tool limitation, by hand): `LIB_VClaims.parent` and `LIB_VClaims.value`. The copy of `value`
is a generic `valueGen P hc` instantiated at the copied `parent`; its equation substitutes the
variable `P`, so no nested proof is transported. -/
namespace NPP_Refine
/-- computable extraction from a total `Result (core.result.Result α E)` whose value is `Ok` -/
def okOkOf {α E : Type} : (r : Aeneas.Std.Result (Aeneas.Std.core.result.Result α E)) →
    (∃ a, r = .ok (.Ok a)) → α
  | .ok (.Ok a), _ => a
  | .ok (.Err _), h => False.elim (h.elim fun _ e => nomatch e)
  | .fail _, h => False.elim (h.elim fun _ e => nomatch e)
  | .div, h => False.elim (h.elim fun _ e => nomatch e)
theorem okOkOf_eq {α E : Type} {r : Aeneas.Std.Result (Aeneas.Std.core.result.Result α E)}
    (h : ∃ a, r = .ok (.Ok a)) {c : α} (e : r = .ok (.Ok c)) : okOkOf r h = c := by subst e; rfl
end NPP_Refine

namespace NPP_C.LIB_VClaims
open Aeneas Aeneas.Std LIB_VCarriers
open AspisR1 ClaimsUnrolledFinish

def parent (p : Prefix) : AspisR1ClaimsUnrolledParent.Claims :=
  NPP_Refine.okOkOf (NJT_ClaimsRef_Value.unbox (NJT_ClaimsRef.r1_semantic.NJT_claims_ref (fromMainPrefix (prefixRaw p))))
    (Exists.imp (fun _ h => h.1) (LIB_VClaimsCanonical.pure_canonical p))

theorem parent.npp_eq : @parent = @_root_.LIB_VClaims.parent := by
  funext p
  exact NPP_Refine.okOkOf_eq _ (_root_.LIB_VClaims.parent_exact p)

/-- `LIB_VClaims.value` with the parent claims and their canonicality as parameters -/
def valueGen (P : Prefix → AspisR1ClaimsUnrolledParent.Claims)
    (hc : ∀ p, LIB_VClaimsCanonical.AllRows (P p)) (p : Prefix) : Claims :=
  ⟨(P p).val.attach.map (fun row => LIB_VArray.lift (toMainArray row.val) (hc p row.val row.property)),
    by simpa using (P p).property⟩

theorem canonical (p : Prefix) : LIB_VClaimsCanonical.AllRows (parent p) := by
  rw [parent.npp_eq]; exact _root_.LIB_VClaims.parent_canonical p

def value (p : Prefix) : Claims := valueGen parent canonical p

theorem value.npp_eq : @value = @_root_.LIB_VClaims.value := by
  have gen : ∀ (P : Prefix → AspisR1ClaimsUnrolledParent.Claims)
      (hc : ∀ p, LIB_VClaimsCanonical.AllRows (P p)), P = _root_.LIB_VClaims.parent →
      valueGen P hc = _root_.LIB_VClaims.value := by
    intro P hc hP; subst hP; rfl
  funext p
  exact congrFun (gen parent canonical parent.npp_eq) p
end NPP_C.LIB_VClaims

/-! A3 (approved): the byte inverse of `LIBB_NullifierBytes.key` (eight little-endian words),
with `decode (key d) = d` proved word by word from `NFY_JFt_DigestInjective.from_to`; the
equation of `digest` follows from injectivity of `key`. -/
namespace NPP_Refine
open Aeneas Aeneas.Std

def word (l : List U8) (i : Nat) : U32 :=
  let c := (l.drop (4 * i)).take 4
  if h : c.length = 4 then core.num.U32.from_le_bytes ⟨c, by rw [h]; rfl⟩ else 0#u32

def decodeDigest (b : RSL.B32) : LIBB_NullifierBytes.Digest :=
  ⟨(List.range 8).map (word (NNC_ByteCarriers.nativeList b.bytes)), by simp⟩

theorem word_chunks (d : LIBB_NullifierBytes.Digest) (i : Nat) (hi : i < 8) :
    word (AspisS6SourceCodec.DigestContents.chunks d) i = d.val[i]'(by rw [d.property]; exact hi) := by
  have sel : ((AspisS6SourceCodec.DigestContents.chunks d).drop (4 * i)).take 4 =
      (core.num.U32.to_le_bytes (d.val[i]'(by rw [d.property]; exact hi))).val := by
    interval_cases i <;>
      simp [AspisS6SourceCodec.DigestContents.chunks, AspisR1.NFY_JFt_DigestInjective.word_length,
        List.drop_append, List.take_append]
  unfold word
  simp only []
  rw [dif_pos (by rw [sel]; exact AspisR1.NFY_JFt_DigestInjective.word_length _)]
  have arr : (⟨((AspisS6SourceCodec.DigestContents.chunks d).drop (4 * i)).take 4, by
      rw [sel]; exact AspisR1.NFY_JFt_DigestInjective.word_length _⟩ : Aeneas.Std.Array U8 4#usize) =
      core.num.U32.to_le_bytes (d.val[i]'(by rw [d.property]; exact hi)) := Subtype.ext sel
  rw [arr]
  exact AspisR1.NFY_JFt_DigestInjective.from_to _

theorem decode_key (d : LIBB_NullifierBytes.Digest) : decodeDigest (LIBB_NullifierBytes.key d) = d := by
  apply Subtype.ext
  change (List.range 8).map (word (NNC_ByteCarriers.nativeList
    (NNC_ByteCarriers.host (AspisS6SourceCodec.DigestContents.chunks d)))) = d.val
  rw [NNC_ByteCarriers.native_host]
  apply List.ext_getElem
  · simp [d.property]
  · intro i h1 h2
    have hi : i < 8 := by simpa using h1
    simp only [List.getElem_map, List.getElem_range]
    exact word_chunks d i hi
end NPP_Refine

namespace NPP_C.LIBB_NullifierBytes
open Aeneas Aeneas.Std

def digest (b : RSL.B32) : Option _root_.LIBB_NullifierBytes.Digest :=
  if _root_.LIBB_NullifierBytes.key (NPP_Refine.decodeDigest b) = b then some (NPP_Refine.decodeDigest b) else none

theorem digest.npp_eq : @digest = @_root_.LIBB_NullifierBytes.digest := by
  funext b
  unfold digest _root_.LIBB_NullifierBytes.digest
  by_cases h : _root_.LIBB_NullifierBytes.key (NPP_Refine.decodeDigest b) = b
  · have ex : ∃ d, _root_.LIBB_NullifierBytes.key d = b := ⟨_, h⟩
    rw [if_pos h, dif_pos ex]
    congr 1
    apply _root_.LIBB_NullifierBytes.injective
    rw [h, Classical.choose_spec ex]
  · have ex : ¬ ∃ d, _root_.LIBB_NullifierBytes.key d = b := by
      rintro ⟨d, hd⟩
      apply h
      rw [← hd, NPP_Refine.decode_key]
    rw [if_neg h, dif_neg ex]
end NPP_C.LIBB_NullifierBytes

#print axioms NPP_C.LIB_VClaims.parent.npp_eq
#print axioms NPP_C.LIB_VClaims.value.npp_eq
#print axioms NPP_Refine.decode_key
#print axioms NPP_C.LIBB_NullifierBytes.digest.npp_eq
#print axioms NPP_C.LIBC_ExpandSemanticModel.Row.npp_eq
#print axioms NPP_C.NJE_WellFrozen.emitted.npp_eq
#print axioms NPP_Refine.decCall
#print axioms NPP_Refine.decDomain
