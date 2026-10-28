import R1Z.ProverCommitPublicNonce40
import R1Z.LayoutR1PBin

/-! A public binding is an existing memo coordinate, not a fresh private
coordinate. These counterexamples identify the exact old freshness interface
that cannot simply be specialised to D152. They do not refute privacy. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitPublicBinding40
open R0Z R0Z.FsStatement R0Z.FsAbort R0Z.FsGood R0Z.HvzkV
open GamesR1PBin LayoutR1PBin
attribute [local instance] Classical.propDecidable

abbrev Private := Fin 2 → NZ

def publicSec (nonce : NZ) (seeds : Private) : SecP := Fin.cases nonce seeds

def binding (pub : List UInt8) (tag : UInt8) (digest nonce : OracleAnswer) : List UInt8 :=
  dBind0 ++ pub ++ [tag] ++ ctxEnc digest nonce

def bindPos (e1 e2 : Nat) : CPos e1 e2 := .inr (.inr (.inl 0))

/-- This is the actual first binding branch of the frozen byte grammar.
Neither private OS seed occurs in it. -/
theorem grammar_binding {e1 e2 : Nat} (pub : List UInt8) (tag : UInt8)
    (lv : Fin 3 → Fib → List UInt8) (digest : OracleAnswer)
    (rest : RIdx → OracleAnswer) (nonce : NZ) (seeds : Private) :
    gram pub tag lv (publicSec nonce seeds) digest rest (bindPos e1 e2) =
      binding pub tag digest nonce.val := by
  simp [gram,publicSec,bindPos,binding]

/-- One adversary query can be this binding, with no knowledge of either seed.
The event is certain on the private-seed carrier, even for a fixed nonce. -/
theorem public_hit_mass (pub : List UInt8) (tag : UInt8)
    (digest : OracleAnswer) (nonce : NZ) :
    eventMass (fun _ : Private =>
      binding pub tag digest nonce.val = binding pub tag digest nonce.val) = 1 := by
  simp only [eventMass,if_true,mean_const]

/-- The old HitFresh interface requires at least 2^255 address-distinguishing
values. On the D152 private carrier this public address is constant. -/
theorem no_hidden_nonce_freshness (pub : List UInt8) (tag : UInt8)
    (digest : OracleAnswer) (nonce : NZ) :
    ¬ R0Z.FsAbortBounds.HitFresh (fun _ : Private => True)
      (fun _ => binding pub tag digest nonce.val)
      (fun _ => binding pub tag digest nonce.val) (2^255) := by
  intro fresh
  have h := R0Z.FsAbortBounds.hitFresh_mass (fun _ : Private => True)
    (fun _ => binding pub tag digest nonce.val)
    (fun _ => binding pub tag digest nonce.val) (2^255) (by positivity) fresh
  have certain : R0Z.FsAbortBounds.mass (fun _ : Private =>
      True ∧ binding pub tag digest nonce.val = binding pub tag digest nonce.val) = 1 := by
    simp [R0Z.FsAbortBounds.mass,mean_const]
  rw [certain] at h
  norm_num at h

/-- No choice of a small seed-guess charge can repair this *public* hit. It
must instead be preserved by the public-prefix ROM coupling. -/
theorem public_hit_exceeds_private_charge (pub : List UInt8) (tag : UInt8)
    (digest : OracleAnswer) (nonce : NZ) :
    4 * ProverCommitPrivateMemo40.budget (2^64) 128 <
      eventMass (fun _ : Private =>
        binding pub tag digest nonce.val = binding pub tag digest nonce.val) := by
  rw [public_hit_mass]
  norm_num [ProverCommitPrivateMemo40.budget]

#print axioms grammar_binding
#print axioms public_hit_mass
#print axioms no_hidden_nonce_freshness
#print axioms public_hit_exceeds_private_charge
end R1Z.ProverCommitPublicBinding40
