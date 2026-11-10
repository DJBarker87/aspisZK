import RPz7_CPG_Projection
import RPz7_CPS_PhysicalKey
import S2W_D189Consolidation
set_option autoImplicit false
noncomputable section
/-! NPN_ (Stream A, gate row 5 scoping job, 2026-11-10). Target not yet established.

First lemma of the recommended non-vacuity route: the recorded-world
construction for one recorded TX1/TX2 pair, at the CPG projection level.

* Data only and parametric in the recorded images. Nothing here evaluates a
  verifier model, and nothing here claims acceptance (`ok1`/`ok2`/`out1`/trace
  are the separate residual, see NPN_NONVACUITY_PLAN.md).
* Global namespace: one index `k` per distinct public key named by either
  transaction; the bank key of account `k`'s data cell is `2*k` and its lamport
  handle is `2*k+1`, so every handle has data cell ≠ lamport cell.
* `pre1` = TX1 pre-images, `post1` = TX1 post-images, used as TX2's bank (the
  recording's isolation check: no other signature touched the accounts between
  the image slots), `post2` = TX2 post-images. The equality of the recorded TX1
  post-image and TX2 pre-image is an offline check of the recording, stated in
  the plan as faithfulness obligation F1, not proved here.
* Field-level correspondence (section 2): every Entry field the host reads
  (key, owner, lamports, signer/writable/executable, rent epoch, data buffer)
  is literally the recorded image or instruction metadata at the recorded cell.
-/
namespace AspisR1.NPN_RecordedFrame
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry Hist_Store Hist_RuntimeEntry
open CPP_BankState CPG_Projection

/-- Inputs of one recorded TX1/TX2 pair (NPC_LOCAL_TRANSACTIONS records). -/
structure Recorded where
  /-- TX1 pre-images: owner and data at key `2k`, lamports at key `2k`. -/
  pre1 : Bank
  /-- TX1 post-images, which are also TX2's pre-images (one literal). -/
  post1 : Bank
  /-- TX2 post-images. -/
  post2 : Bank
  /-- TX1 instruction metadata at cell `2k`: key, signer, writable, executable,
  rent epoch (the landed message header and the account images). -/
  meta1 : Nat → Record
  /-- TX2 (verifier invocation) metadata at cell `2k`. -/
  meta2 : Nat → Record
  /-- TX1 instruction account position → global account index. -/
  cell1 : Nat → Nat
  /-- TX2 verifier-invocation account position → global account index. -/
  cell2 : Nat → Nat
  /-- Serialized input-region addresses and provenance labels (runtime
  serialization layout; computed, not read from the recording). -/
  base1 : Nat → Nat
  prov1 : Nat → Nat
  base2 : Nat → Nat
  prov2 : Nat → Nat
  /-- The 1768 checkpoint bytes TX1 wrote (recorded post-image of account 2). -/
  saved : alloc.vec.Vec U8
  /-- Physical actions after the checkpoint copy, up to parent completion. -/
  actions1 : List (Action Bool)
  actions2 : List (Action Bool)
  events1 : List S2X.AccountEvent
  events2 : List S2X.AccountEvent

/-- Per-invocation layout: account position `i` is global account `cell i`. -/
def layoutOf (cell : Nat → Nat) (md : Nat → Record) (base prov : Nat → Nat) : Layout where
  handles := fun i => (2 * cell i, 2 * cell i + 1)
  records := md
  base := base
  provenance := prov

/-- The recorded projection; transaction `false` is TX1, `true` is TX2. -/
def obs (r : Recorded) : Observations Bool Bool where
  bank := fun b => cond b r.post1 r.pre1
  layout := fun b => cond b (layoutOf r.cell2 r.meta2 r.base2 r.prov2)
    (layoutOf r.cell1 r.meta1 r.base1 r.prov1)
  next := fun t u => t = false ∧ u = true
  intervening := fun _ _ => []
  parentReply := fun _ => .ok (.Ok ())
  copied := fun _ => r.saved
  actions := fun b => cond b r.actions2 r.actions1
  parentTentative := fun b => cond b r.post2 r.post1
  physicalEvents := fun b => cond b r.events2 r.events1

/-- The TX1 and TX2 entries are the CPG projection's entries (game (d)). -/
def e1 (r : Recorded) : Entry := CPG_Projection.entry (obs r) false
def e2 (r : Recorded) : Entry := CPG_Projection.entry (obs r) true

/-! ## 1. Handles -/

theorem e1_handle (r : Recorded) (i : Nat) : (e1 r).handles i = (2 * r.cell1 i, 2 * r.cell1 i + 1) := rfl
theorem e2_handle (r : Recorded) (i : Nat) : (e2 r).handles i = (2 * r.cell2 i, 2 * r.cell2 i + 1) := rfl

/-! ## 2. Field-level correspondence (TX1; TX2 is identical with `pre1 ↦ post1`) -/

theorem e1_key (r : Recorded) (i : Nat) :
    CPS_PhysicalKey.key (e1 r) i = (r.meta1 (2 * r.cell1 i)).owned.key := rfl
theorem e1_owner (r : Recorded) (i : Nat) :
    ((e1 r).records ((e1 r).handles i).1).owned.owner = (r.pre1.cells (2 * r.cell1 i)).owner := rfl
theorem e1_lamports (r : Recorded) (i : Nat) :
    ((e1 r).records ((e1 r).handles i).1).lamports = r.pre1.lamports (2 * r.cell1 i) := rfl
theorem e1_flags (r : Recorded) (i : Nat) :
    ((e1 r).records ((e1 r).handles i).1).owned.is_signer = (r.meta1 (2 * r.cell1 i)).owned.is_signer ∧
    ((e1 r).records ((e1 r).handles i).1).owned.is_writable = (r.meta1 (2 * r.cell1 i)).owned.is_writable ∧
    ((e1 r).records ((e1 r).handles i).1).owned.executable = (r.meta1 (2 * r.cell1 i)).owned.executable ∧
    ((e1 r).records ((e1 r).handles i).1).rentEpoch = (r.meta1 (2 * r.cell1 i)).rentEpoch :=
  ⟨rfl, rfl, rfl, rfl⟩
/-- A live (funded) account's buffer is its recorded data; `cached` empties
only zero-lamport accounts. -/
theorem e1_data (r : Recorded) (i : Nat) (live : r.pre1.lamports (2 * r.cell1 i) ≠ 0) :
    (e1 r).buffers ((e1 r).handles i).1 = (r.pre1.cells (2 * r.cell1 i)).data := by
  change (if r.pre1.lamports (2 * r.cell1 i) = 0 then (⟨[], by simp⟩ : Slice U8)
    else (r.pre1.cells (2 * r.cell1 i)).data) = _
  rw [if_neg live]

theorem e2_key (r : Recorded) (i : Nat) :
    CPS_PhysicalKey.key (e2 r) i = (r.meta2 (2 * r.cell2 i)).owned.key := rfl
theorem e2_owner (r : Recorded) (i : Nat) :
    ((e2 r).records ((e2 r).handles i).1).owned.owner = (r.post1.cells (2 * r.cell2 i)).owner := rfl
theorem e2_lamports (r : Recorded) (i : Nat) :
    ((e2 r).records ((e2 r).handles i).1).lamports = r.post1.lamports (2 * r.cell2 i) := rfl
theorem e2_data (r : Recorded) (i : Nat) (live : r.post1.lamports (2 * r.cell2 i) ≠ 0) :
    (e2 r).buffers ((e2 r).handles i).1 = (r.post1.cells (2 * r.cell2 i)).data := by
  change (if r.post1.lamports (2 * r.cell2 i) = 0 then (⟨[], by simp⟩ : Slice U8)
    else (r.post1.cells (2 * r.cell2 i)).data) = _
  rw [if_neg live]

/-! ## 3. Game (a)-(c) and the two non-trace equalities of (d)

This is exactly the first conjunct of the host GameFrame
(`NNH8_NonVacuity.frame_recorded`) at `p := obs r`, `t := false`, `u := true`,
`i.entry := e1 r`, `j.entry := e2 r`, `saved := r.saved`, `actions := r.actions1`.
The two hypotheses are facts of the recording: TX1 account 2 and TX2 account 6
are the same public key. -/
theorem frame (r : Recorded) (same : r.cell1 2 = r.cell2 6)
    (key : (r.meta1 (2 * r.cell1 2)).owned.key = (r.meta2 (2 * r.cell2 6)).owned.key) :
    ((obs r).next false true ∧ e1 r = CPG_Projection.entry (obs r) false ∧
      e2 r = CPG_Projection.entry (obs r) true) ∧
    ((((obs r).layout false).handles 2).1 = (((obs r).layout true).handles 6).1 ∧
      CPS_PhysicalKey.key (e1 r) 2 = CPS_PhysicalKey.key (e2 r) 6 ∧
      (((obs r).layout false).handles 2).1 ∉ (obs r).intervening false true) ∧
    CPG_Projection.success (obs r) false = true ∧
    (obs r).copied false = r.saved ∧ (obs r).actions false = r.actions1 := by
  refine ⟨⟨⟨rfl, rfl⟩, rfl, rfl⟩, ⟨?_, key, ?_⟩, rfl, rfl, rfl⟩
  · change 2 * r.cell1 2 = 2 * r.cell2 6
    rw [same]
  · intro h
    cases h

/-! ## 4. RuntimeEntrypointAdmission (trust row, here a proved fact of the
recorded entry at the identity library `S2Trust.model`, world := the entry heap) -/

/-- The admission's key function, verbatim. -/
def keys (e : Entry) (a : Nat) : List UInt8 :=
  (e.records (e.handles a).1).owned.key.val.map S2W_ReturnedCheckpoint.nativeByte

theorem valid (e : Entry) (distinct : ∀ a, (e.handles a).1 ≠ (e.handles a).2) : Valid e.heap := by
  refine ⟨List.Pairwise.nil, ?_, ?_, ?_⟩
  · intro c
    simp only [Entry.heap, count, List.filter_nil, List.length_nil, Nat.cast_zero]
    refine ⟨by decide, by decide, by decide, ?_, ?_⟩
    · intro h; exact absurd h (by decide)
    · intro h; exact absurd h (by decide)
  · intro g hg
    cases hg
  · intro a _
    exact ⟨distinct a, rfl⟩

theorem admission (e : Entry) (n : Nat) (cell : Nat → Nat)
    (handles : ∀ a, e.handles a = (2 * cell a, 2 * cell a + 1))
    (inj : ∀ a b, a < n → b < n → keys e a = keys e b → cell a = cell b) :
    S2W_D189Consolidation.RuntimeEntrypointAdmission (S2Trust.model (Nat → Record)) e e.heap n where
  entry :=
    { valid := valid e (fun a => by rw [handles a]; omega)
      freshGuards := rfl
      noExternalBorrows := fun _ => rfl
      liveAccount := fun _ _ => rfl
      counterZero := fun _ _ => rfl
      sharedCellsOnlyEqualKeys := by
        intro a b _ _ h
        change (e.handles a).1 = (e.handles b).1 at h
        change keys e a = keys e b
        unfold keys
        rw [h]
      duplicateKeysShareCell := by
        intro a b ha hb h
        change (e.handles a).1 = (e.handles b).1
        rw [handles a, handles b, inj a b ha hb h] }
  related := rfl

theorem admission1 (r : Recorded)
    (inj : ∀ a b, a < 3 → b < 3 → keys (e1 r) a = keys (e1 r) b → r.cell1 a = r.cell1 b) :
    S2W_D189Consolidation.RuntimeEntrypointAdmission (S2Trust.model (Nat → Record)) (e1 r) (e1 r).heap 3 :=
  admission (e1 r) 3 r.cell1 (fun _ => rfl) inj

theorem admission2 (r : Recorded)
    (inj : ∀ a b, a < 7 → b < 7 → keys (e2 r) a = keys (e2 r) b → r.cell2 a = r.cell2 b) :
    S2W_D189Consolidation.RuntimeEntrypointAdmission (S2Trust.model (Nat → Record)) (e2 r) (e2 r).heap 7 :=
  admission (e2 r) 7 r.cell2 (fun _ => rfl) inj

/-! ## 5. RuntimePersistence (trust row, here a proved fact of the recorded
projection): TX2 loads exactly TX1's final images, for every key. -/

theorem persistence (r : Recorded) (sys : S2W_ExtractionBoundary.Program) :
    CPR_DataPersistence.TwoTransactionLaw (CPG_Projection.adjacent (obs r))
      (CPG_Projection.ordinary (obs r) sys) (CPG_Projection.before (obs r))
      (CPG_Projection.tentative (obs r)) (CPG_Projection.success (obs r))
      (CPG_Projection.loaded (obs r)) := by
  intro t u h key _
  obtain ⟨⟨ht, hu⟩, _⟩ := h
  subst ht
  subst hu
  have s : CPG_Projection.success (obs r) false = true := rfl
  rw [if_pos s]
  rfl

end AspisR1.NPN_RecordedFrame
end
#print axioms AspisR1.NPN_RecordedFrame.e1_key
#print axioms AspisR1.NPN_RecordedFrame.e1_data
#print axioms AspisR1.NPN_RecordedFrame.e2_data
#print axioms AspisR1.NPN_RecordedFrame.frame
#print axioms AspisR1.NPN_RecordedFrame.valid
#print axioms AspisR1.NPN_RecordedFrame.admission
#print axioms AspisR1.NPN_RecordedFrame.admission1
#print axioms AspisR1.NPN_RecordedFrame.admission2
#print axioms AspisR1.NPN_RecordedFrame.persistence
