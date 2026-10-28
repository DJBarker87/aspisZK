import NBN_ValidatorDomains
import NBK_LiveResult
import NBK_AfterstateResult
set_option autoImplicit false
noncomputable section
namespace NBN_FrontierDependency
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder AspisR1.S2K
abbrev Digest := Array U32 8#usize
abbrev Encode := Digest → Array U8 32#usize

/-- Exact named lower bridge needed on caller-proved canonical inputs. -/
def NBN_Dep_DigestEncodeCanonical (encode : Encode) : Prop :=
  ∀ d, NBD_DigestInduction.Canonical d → encode d = DigestBytes.bytes d

/-- The unguarded first-byte helper needs the stronger all-raw lower domain. -/
def NBN_Dep_DigestEncodeRaw (encode : Encode) : Prop :=
  ∀ d, encode d = DigestBytes.bytes d

def liveFold (encode : Encode) : List Digest → Nat → Slice U8 → Slice U8
  | [],_,out => out
  | d::ds,k,out => liveFold encode ds (k+1) (out.setSlice! (160+32*k) (encode d).val)

def afterFold (encode : Encode) : List Digest → Nat → Array U8 688#usize → Array U8 688#usize
  | [],_,out => out
  | d::ds,k,out => afterFold encode ds (k+1) (out.setSlice! (48+32*k) (encode d).val)

theorem live_fold (encode : Encode) (lower : NBN_Dep_DigestEncodeCanonical encode)
    (ds : List Digest) (all : ∀ d ∈ ds, NBD_DigestInduction.Canonical d)
    (k : Nat) (out : Slice U8) :
    liveFold encode ds k out = NBK_LiveBytes.fold ds k out := by
  induction ds generalizing k out with
  | nil => rfl
  | cons d ds ih =>
    have first := lower d (all d (by simp))
    simp only [liveFold,NBK_LiveBytes.fold,first]
    exact ih (fun x hx => all x (by simp [hx])) (k+1) _

theorem after_fold (encode : Encode) (lower : NBN_Dep_DigestEncodeCanonical encode)
    (ds : List Digest) (all : ∀ d ∈ ds, NBD_DigestInduction.Canonical d)
    (k : Nat) (out : Array U8 688#usize) :
    afterFold encode ds k out = AfterstateBytes.fold ds k out := by
  induction ds generalizing k out with
  | nil => rfl
  | cons d ds ih =>
    have first := lower d (all d (by simp))
    simp only [afterFold,AfterstateBytes.fold,first]
    exact ih (fun x hx => all x (by simp [hx])) (k+1) _

theorem rows_canonical (rows : NBH_Frontier.Frontier)
    (all : NBH_Frontier.CanonicalFrom rows 0) :
    ∀ d ∈ rows.val, NBD_DigestInduction.Canonical d := by
  intro d mem
  obtain ⟨i,hi,same⟩ := List.mem_iff_getElem.mp mem
  have bound : i < 20 := by have := rows.property; scalar_tac
  have h := all ⟨i,bound⟩ (by omega)
  simpa only [same] using h

theorem live_caller (encode : Encode) (lower : NBN_Dep_DigestEncodeCanonical encode)
    (s : NBH_LiveValidator.Snapshot) (valid : NBH_LiveValidator.result s = .Ok ())
    (out : Slice U8) :
    encode s.current_root = DigestBytes.bytes s.current_root ∧
    liveFold encode s.frontier.val 0 out = NBK_LiveBytes.fold s.frontier.val 0 out := by
  have domain := NBN_ValidatorDomains.live s valid
  exact ⟨lower _ domain.2.2.2.2.1,
    live_fold encode lower _ (rows_canonical _ domain.2.2.2.2.2) 0 out⟩

theorem after_caller (encode : Encode) (lower : NBN_Dep_DigestEncodeCanonical encode)
    (a : NBH_Validators.Afterstate) (valid : NBH_Validators.afterResult a = .Ok ())
    (out : Array U8 688#usize) :
    encode a.next_root = DigestBytes.bytes a.next_root ∧
    afterFold encode a.next_frontier.val 0 out = AfterstateBytes.fold a.next_frontier.val 0 out := by
  have domain := NBN_ValidatorDomains.afterstate a valid
  exact ⟨lower _ domain.2.2.1,
    after_fold encode lower _ (rows_canonical _ domain.2.2.2) 0 out⟩

#print axioms live_fold
#print axioms after_fold
#print axioms rows_canonical
#print axioms live_caller
#print axioms after_caller
end NBN_FrontierDependency
