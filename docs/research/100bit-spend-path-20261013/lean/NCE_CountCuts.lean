import NBY_CountCarry

set_option autoImplicit false
namespace AspisR1.NCE_CountCuts

/-- One arbitrary count-scan prestate. Other caller state is carried by
`Frame`; native association must instantiate it with the SAME caller carrier. -/
structure ScanState (Frame : Type) where
  key : Nat → Nat
  n : Nat
  parent : Nat
  cursor : Nat
  frame : Frame

/-- The one source test/advance, NOT an entire equal-parent scan. -/
def scanStep {Frame : Type} (s : ScanState Frame) : Bool × ScanState Frame :=
  if s.cursor < s.n ∧ s.key s.cursor / 2 = s.parent then
    (true,{s with cursor := s.cursor+1})
  else (false,s)

/-- Finite machine domain established by the count admission and live-key
invariant. It excludes no reached source scan state. -/
def ScanDomain {Frame : Type} (s : ScanState Frame) : Prop :=
  s.cursor ≤ s.n ∧ s.n ≤ 16 ∧ s.parent < 262144 ∧
    ∀ k, k < s.n → s.key k < 262144

/-- The source test preserves its own native scalar/index domain. -/
theorem scan_step_domain {Frame : Type} (s : ScanState Frame)
    (domain : ScanDomain s) : ScanDomain (scanStep s).2 := by
  unfold scanStep
  split
  next active => exact ⟨by change s.cursor+1 ≤ s.n; omega,domain.2⟩
  next inactive => exact domain

/-- Prospective native contract: exactly one test/advance on arbitrary
prestate, preserving every noncursor component. No final count or scan result. -/
def NCE_Native_CountScan {Frame : Type}
    (native : ScanState Frame → Bool × ScanState Frame) : Prop :=
  ∀ s, ScanDomain s → (native s).1 = decide (s.cursor < s.n ∧ s.key s.cursor / 2 = s.parent) ∧
    (native s).2.cursor = (if s.cursor < s.n ∧ s.key s.cursor / 2 = s.parent
      then s.cursor+1 else s.cursor) ∧
    (∀ k, (native s).2.key k = s.key k) ∧
    (native s).2.n = s.n ∧ (native s).2.parent = s.parent ∧
    (native s).2.frame = s.frame

/-- The pointwise coordinate frame identifies this single native step with
its source-specific model step, without a whole-loop premise. -/
theorem scan_step_eq {Frame : Type}
    (native : ScanState Frame → Bool × ScanState Frame)
    (cut : NCE_Native_CountScan native) (s : ScanState Frame)
    (domain : ScanDomain s) : native s = scanStep s := by
  obtain ⟨test,cursor,key,n,parent,frame⟩ := cut s domain
  have keys : (native s).2.key = s.key := funext key
  have tuple : (native s).2 =
      {s with cursor := if s.cursor < s.n ∧ s.key s.cursor / 2 = s.parent
        then s.cursor+1 else s.cursor} := by
    cases s with
    | mk sk sn sp sc sf =>
      cases h : (native (ScanState.mk sk sn sp sc sf)).2 with
      | mk nk nn np nc nf =>
        simp only [h] at keys n parent cursor frame
        cases keys
        cases n
        cases parent
        cases frame
        cases cursor
        rfl
  apply Prod.ext
  · rw [test]
    unfold scanStep
    split <;> simp_all
  · rw [tuple]
    unfold scanStep
    split <;> rfl

/-- Run only the source's inner loop. The native contract is still for ONE
iteration; this definition makes no Kani whole-loop request. -/
def scanRun {Frame : Type} (native : ScanState Frame → Bool × ScanState Frame) :
    Nat → ScanState Frame → ScanState Frame
  | 0,s => s
  | fuel+1,s => let out := native s
                if out.1 then scanRun native fuel out.2 else out.2

/-- Same key/frame and exact endpoint follow by induction from the one-step
cut. The actual scan recurrence is inherited from NBI, not redefined. -/
theorem scan_run_eq {Frame : Type}
    (native : ScanState Frame → Bool × ScanState Frame)
    (cut : NCE_Native_CountScan native) (fuel : Nat) (s : ScanState Frame)
    (domain : ScanDomain s) :
    scanRun native fuel s = {s with cursor := NBI_CountScan.scan s.key s.parent s.n fuel s.cursor} := by
  induction fuel generalizing s with
  | zero => rfl
  | succ fuel ih =>
    rw [scanRun,scan_step_eq native cut s domain]
    unfold scanStep
    split
    next active =>
      have nextDomain : ScanDomain {s with cursor := s.cursor+1} :=
        ⟨by change s.cursor+1 ≤ s.n; omega,domain.2⟩
      simp only [if_true,NBI_CountScan.scan,if_pos active]
      exact ih _ nextDomain
    next inactive =>
      simp only [Bool.false_eq_true,if_false,NBI_CountScan.scan,if_neg inactive]

/-- The already proved unread-order bound discharges the native caller's
one/two-element group domain; it is not assumed as another caller condition. -/
theorem scan_run_group {Frame : Type}
    (native : ScanState Frame → Bool × ScanState Frame)
    (cut : NCE_Native_CountScan native) (s : ScanState Frame)
    (domain : ScanDomain s)
    (active : s.cursor < s.n)
    (parent : s.parent = s.key s.cursor / 2)
    (ordered : ∀ a b, s.cursor ≤ a → a < b → b < s.n → s.key a < s.key b) :
    let out := scanRun native (s.n-s.cursor) s
    out.cursor = (if s.cursor+1 < s.n ∧ s.key (s.cursor+1)/2 = s.key s.cursor/2
      then s.cursor+2 else s.cursor+1) ∧
    1 ≤ out.cursor-s.cursor ∧ out.cursor-s.cursor ≤ 2 ∧
    out.frame = s.frame ∧ out.key = s.key := by
  have group := NBI_CountScan.scan_group s.key s.n s.cursor active ordered
  rw [scan_run_eq native cut _ s domain]
  dsimp only
  rw [parent]
  rw [group.1]
  exact ⟨rfl,group.2.1,group.2.2,rfl,rfl⟩

/-- Native entry domain follows from the SAME admitted live keys, including
initial copied keys. No independently chosen scan-parent restriction is added. -/
theorem entry_domain {Frame : Type} (key : Nat → Nat) (n i j : Nat)
    (frame : Frame) (small : n ≤ 16) (active : i < n) (cursor : j ≤ n)
    (range : ∀ k, k < n → key k < 262144) :
    ScanDomain (ScanState.mk key n (key i/2) j frame) := by
  have bound := range i active
  have divided := Nat.div_le_self (key i) 2
  exact ⟨cursor,small,by change key i/2 < 262144; omega,range⟩

/-- The copied count entry consumes NBV's existing same-carrier prefix law.
This supplies the actual initialized keys to the prospective scan cut. -/
theorem initialized_entry_domain {Frame : Type} (key : Nat → Nat) (n i j : Nat)
    (frame : Frame) (small : n ≤ 16) (active : i < n) (cursor : j ≤ n)
    (range : ∀ k, k < n → key k < 262144) :
    ScanDomain (ScanState.mk (NBV_CountInitialization.initialized key n) n
      ((NBV_CountInitialization.initialized key n) i/2) j frame) := by
  apply entry_domain _ n i j frame small active cursor
  intro k hk
  rw [NBV_CountInitialization.initialized_cell,if_pos hk]
  exact range k hk

#print axioms entry_domain
#print axioms initialized_entry_domain
#print axioms scan_step_domain
#print axioms scan_step_eq
#print axioms scan_run_eq
#print axioms scan_run_group
end AspisR1.NCE_CountCuts
