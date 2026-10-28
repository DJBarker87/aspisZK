import NBN_FrontierDependency
set_option autoImplicit false
noncomputable section
namespace NBN_DigestResultDependency
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder AspisR1.S2K
abbrev Digest := Array U32 8#usize
abbrev Encode := Digest → Result (Array U8 32#usize)

/-- Full lower law: exact output AND ok status, on each caller-proved domain. -/
def NBN_Dep_DigestEncodeCanonical (encode : Encode) : Prop :=
  ∀ d, NBD_DigestInduction.Canonical d → encode d = ok (DigestBytes.bytes d)

def NBN_Dep_DigestEncodeRaw (encode : Encode) : Prop :=
  ∀ d, encode d = ok (DigestBytes.bytes d)

def foldM {T : Type} (encode : Encode) (store : Nat → Array U8 32#usize → T → T) :
    List Digest → Nat → T → Result T
  | [],_,out => ok out
  | d::ds,k,out => do
    let b ← encode d
    foldM encode store ds (k+1) (store k b out)

def foldModel {T : Type} (store : Nat → Array U8 32#usize → T → T) :
    List Digest → Nat → T → T
  | [],_,out => out
  | d::ds,k,out => foldModel store ds (k+1) (store k (DigestBytes.bytes d) out)

theorem fold_exact {T : Type} (encode : Encode) (lower : NBN_Dep_DigestEncodeCanonical encode)
    (store : Nat → Array U8 32#usize → T → T) (ds : List Digest)
    (domain : ∀ d ∈ ds, NBD_DigestInduction.Canonical d) (k : Nat) (out : T) :
    foldM encode store ds k out = ok (foldModel store ds k out) := by
  induction ds generalizing k out with
  | nil => rfl
  | cons d ds ih =>
    rw [foldM,lower d (domain d (by simp))]
    simp only [bind_tc_ok,foldModel]
    exact ih (fun x hx => domain x (by simp [hx])) (k+1) _

theorem live_model (ds : List Digest) (k : Nat) (out : Slice U8) :
    foldModel (fun i b (o : Slice U8) => o.setSlice! (160+32*i) b.val) ds k out =
      NBK_LiveBytes.fold ds k out := by
  induction ds generalizing k out with
  | nil => rfl
  | cons d ds ih => exact ih (k+1) _

theorem after_model (ds : List Digest) (k : Nat) (out : Array U8 688#usize) :
    foldModel (fun i b (o : Array U8 688#usize) => o.setSlice! (48+32*i) b.val) ds k out =
      AfterstateBytes.fold ds k out := by
  induction ds generalizing k out with
  | nil => rfl
  | cons d ds ih => exact ih (k+1) _

theorem live_caller (encode : Encode) (lower : NBN_Dep_DigestEncodeCanonical encode)
    (s : NBH_LiveValidator.Snapshot) (valid : NBH_LiveValidator.result s = .Ok ()) (out : Slice U8) :
    encode s.current_root = ok (DigestBytes.bytes s.current_root) ∧
    foldM encode (fun i b (o : Slice U8) => o.setSlice! (160+32*i) b.val) s.frontier.val 0 out =
      ok (NBK_LiveBytes.fold s.frontier.val 0 out) := by
  have d := NBN_ValidatorDomains.live s valid
  refine ⟨lower _ d.2.2.2.2.1,?_⟩
  rw [fold_exact encode lower _ _ (NBN_FrontierDependency.rows_canonical _ d.2.2.2.2.2),live_model]

theorem after_caller (encode : Encode) (lower : NBN_Dep_DigestEncodeCanonical encode)
    (s : NBH_Validators.Afterstate) (valid : NBH_Validators.afterResult s = .Ok ()) (out : Array U8 688#usize) :
    encode s.next_root = ok (DigestBytes.bytes s.next_root) ∧
    foldM encode (fun i b (o : Array U8 688#usize) => o.setSlice! (48+32*i) b.val) s.next_frontier.val 0 out =
      ok (AfterstateBytes.fold s.next_frontier.val 0 out) := by
  have d := NBN_ValidatorDomains.afterstate s valid
  refine ⟨lower _ d.2.2.1,?_⟩
  rw [fold_exact encode lower _ _ (NBN_FrontierDependency.rows_canonical _ d.2.2.2),after_model]

#print axioms fold_exact
#print axioms live_model
#print axioms after_model
#print axioms live_caller
#print axioms after_caller
end NBN_DigestResultDependency
