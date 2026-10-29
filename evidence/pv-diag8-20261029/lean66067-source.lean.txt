import PV_DIAG8_Publication
set_option autoImplicit false
namespace PV_DIAG8
/-! Literal error-construction sites of the actual proof-account client.
Formatting OS replies and arbitrary Debug implementations remains separate. -/
inductive ClientGuard
 | legacy | listType | listCount | keyType | keyCanonical | duplicate
 | position | attempts | lane | checkpoint | anchor | settled | marker | unknown
 deriving DecidableEq
 def guardText : ClientGuard → String
 | .legacy => "legacy proof_account input is unsupported"
 | .listType => "proof_accounts must be eight public keys"
 | .listCount => "proof_accounts must contain eight public keys"
 | .keyType => "proof account must be a string"
 | .keyCanonical => "noncanonical/zero proof account"
 | .duplicate => "duplicate proof account"
 | .position => "unexpected settlement proof-account position"
 | .attempts => "invalid successful attempt count"
 | .lane => "wrong live output lane"
 | .checkpoint => "checkpoint master mismatch"
 | .anchor => "deposits do not reconstruct finalized anchor"
 | .settled => "settled lane differs from proved afterstate"
 | .marker => "consumed marker identity differs"
 | .unknown => "unknown action"

theorem message_fixed_at_site {W : Type} (site : ClientGuard) (w w' : W) : (fun _ : W => guardText site) w = (fun _ : W => guardText site) w' := rfl
#print axioms message_fixed_at_site
-- NEXT
theorem message_site_law (a b : ClientGuard) (h : a=b) : guardText a = guardText b := congrArg guardText h
#print axioms message_site_law
-- NEXT
theorem message_no_dynamic_operands (g : ClientGuard) : ∃ text : String, guardText g = text := ⟨guardText g,rfl⟩
#print axioms message_no_dynamic_operands
-- NEXT
theorem message_length_law (a b : ClientGuard) (h : a=b) : (guardText a).utf8ByteSize=(guardText b).utf8ByteSize := congrArg String.utf8ByteSize (message_site_law a b h)
#print axioms message_length_law
-- NEXT
theorem message_public_history {P W : Type} (sites : P → List ClientGuard) (p : P) (w w' : W) : (fun _ : W => (sites p).map guardText) w = (fun _ : W => (sites p).map guardText) w' := rfl
#print axioms message_public_history
-- NEXT
theorem message_error_prefix (sites : List ClientGuard) (n : Nat) : (sites.take n).map guardText = (sites.map guardText).take n := by simp only [List.map_take]
#print axioms message_error_prefix
-- NEXT
theorem message_prefix_count (sites : List ClientGuard) : (sites.map guardText).length=sites.length := by simp
#print axioms message_prefix_count
-- NEXT
theorem message_capture_site_separate (a b : ClientGuard) (h : a=b) : (a,guardText a)=(b,guardText b) := by cases h; rfl
#print axioms message_capture_site_separate
end PV_DIAG8
