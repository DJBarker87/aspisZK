import R1Z.SimCostWriter

/-! Costed replay of GamesR1.runLog and its programmed oracle. Byte comparison
is charged by both key lengths. Adversary computation between queries and
wire/view construction are separate stages, not hidden in the query tariff. -/
set_option autoImplicit false
namespace R1Z.SimCostReplay
open R0Z.FsStatement R1Z.SimCostWriter R1Z.GamesR1 R1Z.TranscriptR1
abbrev Bytes := List UInt8
abbrev Table := List (Bytes × OracleAnswer)

def lookup (a : Bytes) : Table → Costed (Option OracleAnswer)
  | [] => (none, 1)
  | (b,v)::t => if a = b then (some v, a.length+b.length+3)
      else let r := lookup a t; (r.1, a.length+b.length+3+r.2)

theorem lookup_erase (a : Bytes) (t : Table) : (lookup a t).1 = t.lookup a := by
  induction t with
  | nil => rfl
  | cons b t ih =>
    rcases b with ⟨b,v⟩
    by_cases he : a = b
    · subst b; simp [lookup]
    · have hbe : (a == b) = false := beq_eq_false_iff_ne.mpr he
      simp only [lookup, if_neg he, ih, List.lookup, hbe]

def KeysBound (L : Nat) (t : Table) : Prop := ∀ b v, (b,v) ∈ t → b.length ≤ L

theorem lookup_bound (a : Bytes) (t : Table) (L : Nat)
    (ha : a.length ≤ L) (ht : KeysBound L t) :
    (lookup a t).2 ≤ (t.length+1)*(2*L+3) := by
  induction t with
  | nil => simp only [lookup, List.length_nil]; omega
  | cons b t ih =>
    rcases b with ⟨b,v⟩
    have hb := ht b v (List.mem_cons_self)
    have hi := ih (fun c w hc => ht c w (List.mem_cons_of_mem _ hc))
    simp only [lookup, List.length_cons]
    split <;> dsimp only <;> nlinarith

/-- One fresh underlying oracle query on a miss. -/
def oracle (t : Table) (H : Bytes → OracleAnswer) (a : Bytes) : Costed OracleAnswer :=
  let r := lookup a t
  (r.1.getD (H a), r.2+1)

theorem oracle_erase (t : Table) (H : Bytes → OracleAnswer) (a : Bytes) :
    (oracle t H a).1 = (t.lookup a).getD (H a) := by
  change (lookup a t).1.getD (H a) = _
  rw [lookup_erase]

/-- The pair insert records the adversary's query/answer; a control tick is
also paid. The adversary continuation is oracle-machine external work. -/
def replay (t : Table) (H : Bytes → OracleAnswer) : OProg → Nat → Costed Table
  | .done, _ => ([], 0)
  | .query _ _, 0 => ([], 0)
  | .query a k, n+1 =>
    let ans := oracle t H a
    let rest := replay t H (k ans.1) n
    ((a,ans.1)::rest.1, ans.2+rest.2+2)

theorem replay_erase (t : Table) (H : Bytes → OracleAnswer) (p : OProg) (q : Nat) :
    (replay t H p q).1 = runLog p (fun a => (t.lookup a).getD (H a)) q := by
  induction q generalizing p with
  | zero => cases p <;> rfl
  | succ q ih =>
    cases p with
    | done => rfl
    | query a k =>
      simp only [replay, runLog, oracle_erase, ih]

/-- Bounds are needed only on the addresses actually reached. -/
def AddressBound (O : Bytes → OracleAnswer) (L : Nat) : OProg → Nat → Prop
  | .done, _ => True
  | .query _ _, 0 => True
  | .query a k, n+1 => a.length ≤ L ∧ AddressBound O L (k (O a)) n

theorem replay_bound (t : Table) (H : Bytes → OracleAnswer) (p : OProg) (q L : Nat)
    (ht : KeysBound L t)
    (hp : AddressBound (fun a => (t.lookup a).getD (H a)) L p q) :
    (replay t H p q).2 ≤ q*((t.length+1)*(2*L+3)+3) := by
  induction q generalizing p with
  | zero => cases p <;> simp [replay]
  | succ q ih =>
    cases p with
    | done => simp [replay]
    | query a k =>
      obtain ⟨ha,hp⟩ := hp
      have hb := lookup_bound a t L ha ht
      have hr := ih (k ((t.lookup a).getD (H a))) hp
      simp only [replay, oracle_erase]
      change (lookup a t).2+1 + (replay t H (k ((t.lookup a).getD (H a))) q).2+2 ≤ _
      nlinarith

/-- Programming and table insertion each cost one tick per programmed row.
This bound is linear in q for fixed protocol key length and table size. -/
def programmed (t : Table) (H : Bytes → OracleAnswer) (p : OProg) (q : Nat) : Costed Table :=
  ((replay t H p q).1, 2*t.length+(replay t H p q).2)

theorem programmed_erase (t : Table) (H : Bytes → OracleAnswer) (p : OProg) (q : Nat) :
    (programmed t H p q).1 = runLog p (fun a => (t.lookup a).getD (H a)) q :=
  replay_erase t H p q

theorem programmed_linear (t : Table) (H : Bytes → OracleAnswer) (p : OProg) (q L : Nat)
    (ht : KeysBound L t)
    (hp : AddressBound (fun a => (t.lookup a).getD (H a)) L p q) :
    (programmed t H p q).2 ≤ ((t.length+1)*(2*L+3)+2*t.length+3)*(q+1) := by
  have hb := replay_bound t H p q L ht hp
  change 2*t.length+(replay t H p q).2 ≤ _
  nlinarith

#print axioms lookup_erase
#print axioms lookup_bound
#print axioms oracle_erase
#print axioms replay_erase
#print axioms replay_bound
#print axioms programmed_erase
#print axioms programmed_linear
end R1Z.SimCostReplay
