/-!
# Reachability invariant for the V7 terminal PDA certificate

The production APD8 initializer first runs canonical descending PDA search,
persists the resulting address and bump in a verifier-owned account, and then
replays the single-attempt derivation.  Terminal execution never writes that
account.  This file proves the representation-independent induction consumed
by the source-closure audit: every reachable certificate is canonical, every
successful preservation step keeps it canonical, and replacing search by the
recorded single attempt has the same accept/reject relation on reachable
states.

`scripts/v7_terminal_pda_inventory.py` separately pins the literal Rust
initializer, immutable write surface, terminal readers, exact seeds, and
program identifiers.  This theorem does not claim that a handwritten address
function is Solana's implementation; the `CanonicalDerivation` premise is the
precise source boundary discharged by the initializer's search-then-replay
check.
-/

set_option autoImplicit false

namespace AspisPool.V7TerminalPdaCertificateInvariant

/-- The twelve literal APD8 slots initialized and replayed by
`v7_terminal_pda_certificate.rs`. Optional next-page and custody slots remain
in this closed class list; their runtime flags decide whether they are read. -/
inductive PdaClass where
  | master
  | checkpoint
  | selectedLane
  | currentHistoryPage
  | nextHistoryPage
  | nullifierMarker
  | registry
  | registryProgramData
  | registryEntry
  | verifierProgramData
  | vaultAuthority
  | vaultToken
deriving DecidableEq

def allPdaClasses : List PdaClass :=
  [.master, .checkpoint, .selectedLane, .currentHistoryPage,
   .nextHistoryPage, .nullifierMarker, .registry, .registryProgramData,
   .registryEntry, .verifierProgramData, .vaultAuthority, .vaultToken]

theorem all_pda_classes_count : allPdaClasses.length = 12 := by
  rfl

/-- Abstract exact seed list plus program identifier. -/
structure PdaIdentity (ProgramId Seed : Type) where
  programId : ProgramId
  seeds : List Seed
deriving DecidableEq

/-- The relationship enforced in the APD8 initializer between Solana's
canonical descending search and one `create_program_address` attempt. -/
structure CanonicalDerivation
    (Identity Address Bump : Type) where
  search : Identity → Address × Bump
  create : Identity → Bump → Option Address
  search_replays : ∀ identity,
    create identity (search identity).2 = some (search identity).1

/-- One persisted address/bump entry.  APD8 contains twelve of these entries;
the theorem is pointwise and therefore lifts directly with `List.Forall`. -/
structure PersistedBump (Identity Address Bump : Type) where
  identity : Identity
  address : Address
  bump : Bump
deriving DecidableEq

def IsCanonical
    {Identity Address Bump : Type}
    (derivation : CanonicalDerivation Identity Address Bump)
    (entry : PersistedBump Identity Address Bump) : Prop :=
  derivation.search entry.identity = (entry.address, entry.bump)

/-- The closed verifier-owned writer surface. `initialize` is the only write
of new bytes; all other successful transitions preserve the exact image. -/
inductive AuthenticatedCertificateWriter
    {Identity Address Bump : Type}
    (derivation : CanonicalDerivation Identity Address Bump) :
    Option (PersistedBump Identity Address Bump) →
      PersistedBump Identity Address Bump → Prop where
  | initialized (identity : Identity) :
      AuthenticatedCertificateWriter derivation none {
        identity := identity
        address := (derivation.search identity).1
        bump := (derivation.search identity).2
      }
  | preserved (entry : PersistedBump Identity Address Bump) :
      AuthenticatedCertificateWriter derivation (some entry) entry

/-- Reachability begins with a zeroed account and can cross into an initialized
state exactly once.  Later successful program-owned steps are byte-exact
preservations. -/
inductive CertificateReachable
    {Identity Address Bump : Type}
    (derivation : CanonicalDerivation Identity Address Bump) :
    Option (PersistedBump Identity Address Bump) → Prop where
  | zeroed : CertificateReachable derivation none
  | step
      {before : Option (PersistedBump Identity Address Bump)}
      {after : PersistedBump Identity Address Bump}
      (beforeReachable : CertificateReachable derivation before)
      (writer : AuthenticatedCertificateWriter derivation before after) :
      CertificateReachable derivation (some after)

theorem initialized_entry_is_canonical
    {Identity Address Bump : Type}
    (derivation : CanonicalDerivation Identity Address Bump)
    (identity : Identity) :
    IsCanonical derivation {
      identity := identity
      address := (derivation.search identity).1
      bump := (derivation.search identity).2
    } := by
  rfl

private theorem reachable_some_is_canonical
    {Identity Address Bump : Type}
    (derivation : CanonicalDerivation Identity Address Bump)
    {state : Option (PersistedBump Identity Address Bump)}
    (reachable : CertificateReachable derivation state) :
    ∀ entry, state = some entry → IsCanonical derivation entry := by
  induction reachable with
  | zeroed =>
      intro entry impossible
      cases impossible
  | @step before after beforeReachable writer inductionHypothesis =>
      intro entry equality
      cases writer with
      | initialized identity =>
          cases equality
          rfl
      | preserved preserved =>
          cases equality
          exact inductionHypothesis _ rfl

/-- Every reachable persisted APD8 entry was either initialized from the exact
canonical search result or preserved byte-for-byte from such an entry. -/
theorem reachable_persisted_bump_is_canonical
    {Identity Address Bump : Type}
    (derivation : CanonicalDerivation Identity Address Bump)
    {entry : PersistedBump Identity Address Bump}
    (reachable : CertificateReachable derivation (some entry)) :
    IsCanonical derivation entry :=
  reachable_some_is_canonical derivation reachable entry rfl

theorem successful_writer_preserves_canonicality
    {Identity Address Bump : Type}
    (derivation : CanonicalDerivation Identity Address Bump)
    {before : Option (PersistedBump Identity Address Bump)}
    {after : PersistedBump Identity Address Bump}
    (beforeReachable : CertificateReachable derivation before)
    (writer : AuthenticatedCertificateWriter derivation before after) :
    IsCanonical derivation after := by
  exact reachable_persisted_bump_is_canonical derivation
    (.step beforeReachable writer)

/-- A terminal single-attempt replay of a reachable certificate returns the
same canonical address produced by the old runtime search. -/
theorem reachable_single_attempt_returns_canonical_address
    {Identity Address Bump : Type}
    (derivation : CanonicalDerivation Identity Address Bump)
    {entry : PersistedBump Identity Address Bump}
    (reachable : CertificateReachable derivation (some entry)) :
    derivation.create entry.identity entry.bump = some entry.address := by
  have canonical := reachable_persisted_bump_is_canonical derivation reachable
  unfold IsCanonical at canonical
  have addressEq : (derivation.search entry.identity).1 = entry.address := by
    simpa using congrArg Prod.fst canonical
  have bumpEq : (derivation.search entry.identity).2 = entry.bump := by
    simpa using congrArg Prod.snd canonical
  rw [← addressEq, ← bumpEq]
  exact derivation.search_replays entry.identity

def SearchAccepts
    {Identity Address Bump : Type}
    (derivation : CanonicalDerivation Identity Address Bump)
    (identity : Identity) (supplied : Address) : Prop :=
  (derivation.search identity).1 = supplied

def CertifiedSingleAttemptAccepts
    {Identity Address Bump : Type}
    (derivation : CanonicalDerivation Identity Address Bump)
    (entry : PersistedBump Identity Address Bump)
    (identity : Identity) (supplied : Address) : Prop :=
  entry.identity = identity ∧ entry.address = supplied ∧
    derivation.create identity entry.bump = some supplied

/-- Exact accept/reject preservation for every reachable authenticated APD8
entry.  Identity equality and address comparison remain explicit checks. -/
theorem reachable_search_iff_certified_single_attempt
    {Identity Address Bump : Type}
    (derivation : CanonicalDerivation Identity Address Bump)
    {entry : PersistedBump Identity Address Bump}
    (reachable : CertificateReachable derivation (some entry))
    (identity : Identity) (supplied : Address) :
    (entry.identity = identity ∧ SearchAccepts derivation identity supplied) ↔
      CertifiedSingleAttemptAccepts derivation entry identity supplied := by
  constructor
  · rintro ⟨identityEq, searchEq⟩
    subst identity
    have canonical := reachable_persisted_bump_is_canonical derivation reachable
    unfold IsCanonical at canonical
    have addressEq : entry.address = supplied := by
      rw [← searchEq]
      simpa using (congrArg Prod.fst canonical).symm
    refine ⟨rfl, addressEq, ?_⟩
    rw [← addressEq]
    exact reachable_single_attempt_returns_canonical_address derivation reachable
  · rintro ⟨identityEq, addressEq, _⟩
    subst identity
    refine ⟨rfl, ?_⟩
    unfold SearchAccepts
    have canonical := reachable_persisted_bump_is_canonical derivation reachable
    unfold IsCanonical at canonical
    rw [← addressEq]
    simpa using congrArg Prod.fst canonical

/-- Corruption fails closed whenever the changed bump does not recreate the
recorded canonical address. This is exactly the runtime comparison performed
after `create_program_address`; no uniqueness of noncanonical bumps is
assumed. -/
theorem corrupted_bump_that_does_not_recreate_address_rejects
    {Identity Address Bump : Type}
    (derivation : CanonicalDerivation Identity Address Bump)
    (entry : PersistedBump Identity Address Bump)
    (corruptBump : Bump)
    (failsReplay :
      derivation.create entry.identity corruptBump ≠ some entry.address) :
    ¬ CertifiedSingleAttemptAccepts derivation
      { entry with bump := corruptBump } entry.identity entry.address := by
  intro accepted
  exact failsReplay accepted.2.2

theorem all_reachable_certificate_entries_are_canonical
    {Identity Address Bump : Type}
    (derivation : CanonicalDerivation Identity Address Bump)
    (entries : List (PersistedBump Identity Address Bump))
    (reachable : ∀ entry ∈ entries,
      CertificateReachable derivation (some entry)) :
    ∀ entry ∈ entries, IsCanonical derivation entry := by
  intro entry member
  exact reachable_persisted_bump_is_canonical derivation
    (reachable entry member)

/-- The pointwise induction covers every one of the twelve source slots, not
merely a representative address. -/
theorem every_apd8_class_is_canonical
    {Address Bump : Type}
    (derivation : CanonicalDerivation PdaClass Address Bump)
    (image : PdaClass → PersistedBump PdaClass Address Bump)
    (identityExact : ∀ slot, (image slot).identity = slot)
    (reachable : ∀ slot,
      CertificateReachable derivation (some (image slot))) :
    ∀ slot ∈ allPdaClasses, IsCanonical derivation (image slot) := by
  intro slot _
  have canonical := reachable_persisted_bump_is_canonical derivation
    (reachable slot)
  have _ := identityExact slot
  exact canonical

#print axioms initialized_entry_is_canonical
#print axioms reachable_persisted_bump_is_canonical
#print axioms successful_writer_preserves_canonicality
#print axioms reachable_single_attempt_returns_canonical_address
#print axioms reachable_search_iff_certified_single_attempt
#print axioms corrupted_bump_that_does_not_recreate_address_rejects
#print axioms all_reachable_certificate_entries_are_canonical
#print axioms all_pda_classes_count
#print axioms every_apd8_class_is_canonical

end AspisPool.V7TerminalPdaCertificateInvariant
