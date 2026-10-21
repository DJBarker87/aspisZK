import R1Z.SimCostReplay

/-! D116: oracle-machine overhead relative to the adversary's actual queried
bytes. GamesR1.R1Adv has no internal running-time semantics. The parameter q
is the experiment's query cap; bytes counts only queries reached on this run.
No length restriction is imposed on adversary addresses. -/
set_option autoImplicit false
namespace R1Z.SimCostRelativeReplay
open R0Z.FsStatement R1Z.GamesR1 R1Z.SimCostReplay

/-- Total input bytes submitted by the adversary on this adaptive path. -/
def queryBytes (O : List UInt8 → OracleAnswer) : OProg → Nat → Nat
  | .done, _ => 0
  | .query _ _, 0 => 0
  | .query a k, n+1 => a.length + queryBytes O (k (O a)) n

def inputLength (O : List UInt8 → OracleAnswer) (p : OProg) (q : Nat) : Nat :=
  q + queryBytes O p q

theorem queryBytes_log (O : List UInt8 → OracleAnswer) (p : OProg) (q : Nat) :
    queryBytes O p q = ((runLog p O q).map (fun row => row.1.length)).sum := by
  induction q generalizing p with
  | zero => cases p <;> rfl
  | succ q ih => cases p with
    | done => rfl
    | query a k => simp only [queryBytes, runLog, List.map_cons, List.sum_cons, ih]

/-- Only stored keys require a protocol bound. The queried key is paid by n. -/
theorem lookup_bytes (a : List UInt8) (t : Table) (L : Nat) (ht : KeysBound L t) :
    (lookup a t).2 ≤ (t.length+1)*(a.length+L+3) := by
  induction t with
  | nil => simp only [lookup, List.length_nil]; omega
  | cons b t ih =>
    rcases b with ⟨b,v⟩
    have hb := ht b v List.mem_cons_self
    have hi := ih (fun c w hc => ht c w (List.mem_cons_of_mem _ hc))
    simp only [lookup, List.length_cons]
    split <;> dsimp only <;> nlinarith

theorem replay_bytes (t : Table) (H : List UInt8 → OracleAnswer) (p : OProg) (q L : Nat)
    (ht : KeysBound L t) :
    (replay t H p q).2 ≤ (t.length+1) *
      (queryBytes (fun a => (t.lookup a).getD (H a)) p q + q*(L+6)) := by
  induction q generalizing p with
  | zero => cases p <;> simp only [replay, queryBytes] <;> omega
  | succ q ih => cases p with
    | done => simp only [replay, queryBytes]; positivity
    | query a k =>
      have hb := lookup_bytes a t L ht
      have hr := ih (k ((t.lookup a).getD (H a)))
      simp only [replay, oracle_erase, queryBytes]
      change (lookup a t).2+1 + (replay t H (k ((t.lookup a).getD (H a))) q).2+2 ≤ _
      nlinarith

theorem replay_relative (t : Table) (H : List UInt8 → OracleAnswer) (p : OProg) (q L : Nat)
    (ht : KeysBound L t) :
    (replay t H p q).2 ≤ (t.length+1)*(L+6) *
      inputLength (fun a => (t.lookup a).getD (H a)) p q := by
  have hb := replay_bytes t H p q L ht
  have hm : queryBytes (fun a => (t.lookup a).getD (H a)) p q + q*(L+6) ≤
      (L+6) * (q + queryBytes (fun a => (t.lookup a).getD (H a)) p q) := by
    nlinarith
  exact hb.trans (by
    unfold inputLength
    calc
      _ ≤ (t.length+1)*((L+6)*(q + queryBytes (fun a => (t.lookup a).getD (H a)) p q)) :=
        Nat.mul_le_mul_left _ hm
      _ = _ := by ring)

theorem programmed_relative (t : Table) (H : List UInt8 → OracleAnswer) (p : OProg) (q L : Nat)
    (ht : KeysBound L t) :
    (programmed t H p q).2 ≤ ((t.length+1)*(L+6)+2*t.length) *
      (inputLength (fun a => (t.lookup a).getD (H a)) p q + 1) := by
  have hb := replay_relative t H p q L ht
  change 2*t.length + (replay t H p q).2 ≤ _
  nlinarith

#print axioms queryBytes_log
#print axioms lookup_bytes
#print axioms replay_bytes
#print axioms replay_relative
#print axioms programmed_relative
end R1Z.SimCostRelativeReplay
