import NHJ_SdkBorrowPacket
set_option autoImplicit false
namespace NHJ_SdkDomains
open AspisR1.S2Trust

def bound (field : Guard → Nat) : List Guard → Nat
  | [] => 0
  | g::rest => field g + bound field rest

theorem member_bound (field : Guard → Nat) (guards : List Guard) :
    ∀ g ∈ guards, field g ≤ bound field guards := by
  induction guards with
  | nil => simp
  | cons first rest ih =>
    intro g member
    simp only [List.mem_cons] at member
    rcases member with rfl | member
    · simp [bound]
    · have smaller := ih g member
      simp only [bound]
      omega

theorem not_found (guards : List Guard) (token : Nat)
    (different : ∀ g ∈ guards, g.token ≠ token) :
    guards.find? (fun g => g.token == token) = none := by
  induction guards with
  | nil => rfl
  | cons first rest ih =>
    have head := different first (by simp)
    have tail : ∀ g ∈ rest, g.token ≠ token := by
      intro g member
      exact different g (by simp [member])
    simp [List.find?_cons,head,ih tail]

/-- A valid caller need not assume an empty live-guard list. Tokens and owners
are fresh logical affine names, selected from the finite existing set. -/
theorem enabled_exists {F : Type} (s : Heap F) (account : Nat)
    (live : s.ownerLive account = true) :
    ∃ token owner, Enabled s (.shared account token owner) := by
  let token := bound Guard.token s.guards + 1
  let owner := bound Guard.owner s.guards + 1
  refine ⟨token,owner,live,not_found s.guards token ?_,?_⟩
  · intro g member
    have before := member_bound Guard.token s.guards g member
    dsimp [token]
    omega
  · intro g member
    have before := member_bound Guard.owner s.guards g member
    dsimp [owner]
    omega

theorem counter_cases {F : Type} (s : Heap F) (valid : Valid s) (account : Nat) :
    (0 ≤ s.counter (s.accounts account).1 ∧ s.counter (s.accounts account).1 < maxCounter) ∨
    (s.counter (s.accounts account).1 < 0 ∨ s.counter (s.accounts account).1 = maxCounter) := by
  have upper := (valid.2.1 (s.accounts account).1).2.1
  omega
#print axioms member_bound
#print axioms not_found
#print axioms enabled_exists
#print axioms counter_cases
end NHJ_SdkDomains
