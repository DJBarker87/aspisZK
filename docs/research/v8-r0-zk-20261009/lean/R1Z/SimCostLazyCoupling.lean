import R1Z.GamesR1PBin
import R1Z.LazyTable

/-! Exact lazy-ROM coupling for the actual adaptive OProg, including repeated
addresses and arbitrary key decoding. The executable side reads at most q
independent uniform 256-bit answers; it never materialises a full ROM table.
This law does not implement or couple the simulator's uniform field tape. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.SimCostLazyCoupling
open R0Z R0Z.FsStatement R0Z.FsAbortBounds R1Z.GamesR1
variable {A : Type} [DecidableEq A]

/-- A finite persistent cache is represented by a chain of updates to the
initial partial map. Only the fresh-answer count is charged in this module. -/
def cached (c : A → Option OracleAnswer) (H : A → OracleAnswer) (a : A) : OracleAnswer :=
  (c a).getD (H a)

def lazyRun (key : List UInt8 → A) (c : A → Option OracleAnswer) (p : OProg) :
    (q : Nat) → (Fin q → OracleAnswer) →
      (List (List UInt8 × OracleAnswer) × Nat)
  | 0, _ => ([],0)
  | q+1, u => match p with
    | .done => ([],0)
    | .query a k => match c (key a) with
      | some v =>
        let r := lazyRun key c (k v) q (Fin.init u)
        ((a,v)::r.1,r.2)
      | none =>
        let v := u (Fin.last q)
        let r := lazyRun key (Function.update c (key a) (some v)) (k v) q (Fin.init u)
        ((a,v)::r.1,r.2+1)

theorem lazy_draws (key : List UInt8 → A) (c : A → Option OracleAnswer)
    (p : OProg) (q : Nat) (u : Fin q → OracleAnswer) :
    (lazyRun key c p q u).2 ≤ q := by
  induction q generalizing c p with
  | zero => simp only [lazyRun, le_refl]
  | succ q ih =>
    cases p with
    | done => exact Nat.zero_le _
    | query a k =>
      cases he : c (key a) with
      | none =>
        simpa only [lazyRun, he] using (Nat.add_le_add_right
          (ih (Function.update c (key a) (some (u (Fin.last q))))
            (k (u (Fin.last q))) (Fin.init u)) 1)
      | some v =>
        simpa only [lazyRun, he] using
          (ih c (k v) (Fin.init u)).trans (Nat.le_succ q)

/-- A single fresh coordinate can be resampled independently. -/
theorem mean_update [Fintype A] (a : A) (f : (A → OracleAnswer) → ℚ) :
    mean (fun p : (A → OracleAnswer) × OracleAnswer =>
      f (Function.update p.1 a p.2)) = mean f := by
  unfold mean
  rw [Fintype.sum_prod_type, LazyTable.sum_update, Fintype.card_prod, Nat.cast_mul]
  have hu : (Fintype.card OracleAnswer : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [mul_comm (Fintype.card (A → OracleAnswer) : ℚ)]
  exact mul_div_mul_left _ _ hu

/-- Split off one independent answer without enumerating the answer space. -/
theorem mean_snoc {T : Type} [Fintype T] (q : Nat) (f : (Fin (q+1) → T) → ℚ) :
    mean f = mean (fun v : T => mean (fun u : Fin q → T => f (Fin.snoc u v))) := by
  rw [mean_equiv' (Fin.snocEquiv (fun _ => T)).symm, LawTransport.mean_product]
  rfl

theorem mean_swap {S T : Type} [Fintype S] [Fintype T] (f : S → T → ℚ) :
    mean (fun s => mean (f s)) = mean (fun t => mean (fun s => f s t)) := by
  calc
    _ = mean (fun p : S × T => f p.1 p.2) :=
      (LawTransport.mean_product _).symm
    _ = mean (fun p : T × S => f p.2 p.1) :=
      mean_equiv' (Equiv.prodComm S T) _
    _ = _ := LawTransport.mean_product _

theorem cached_update (c : A → Option OracleAnswer) (H : A → OracleAnswer)
    (a : A) (v : OracleAnswer) (ha : c a = none) :
    cached c (Function.update H a v) = cached (Function.update c a (some v)) H := by
  funext b
  by_cases hb : b = a
  · subst b; simp only [cached, ha, Function.update_self, Option.getD_none, Option.getD_some]
  · simp only [cached, Function.update_of_ne hb]

/-- Equality of all rational observer expectations, not just a value-erasure
claim. Cache hits reuse their answer. Initial programmed cells are retained.
The key map may identify labels, e.g. all out-of-domain byte strings. -/
theorem lazy_uniform [Fintype A] (key : List UInt8 → A)
    (c : A → Option OracleAnswer) (p : OProg) (q : Nat)
    (f : List (List UInt8 × OracleAnswer) → ℚ) :
    mean (fun u : Fin q → OracleAnswer => f (lazyRun key c p q u).1) =
      mean (fun H : A → OracleAnswer => runLog p (fun a => cached c H (key a)) q |> f) := by
  induction q generalizing c p f with
  | zero => cases p <;> simp only [lazyRun, runLog, mean_const']
  | succ q ih =>
    cases p with
    | done => simp only [lazyRun, runLog, mean_const']
    | query a k =>
      rw [mean_snoc q]
      cases hc : c (key a) with
      | some v =>
        simp only [lazyRun, hc, Fin.init_snoc]
        change mean (fun _ : OracleAnswer => mean (fun u : Fin q → OracleAnswer =>
          f ((a,v)::(lazyRun key c (k v) q u).1))) = _
        rw [ih c (k v) (fun log => f ((a,v)::log)), mean_const']
        simp only [runLog, cached, hc, Option.getD_some]
      | none =>
        simp only [lazyRun, hc, Fin.snoc_last, Fin.init_snoc]
        change mean (fun v : OracleAnswer => mean (fun u : Fin q → OracleAnswer =>
          f ((a,v)::(lazyRun key (Function.update c (key a) (some v)) (k v) q u).1))) = _
        have inner (v : OracleAnswer) :=
          ih (Function.update c (key a) (some v)) (k v) (fun log => f ((a,v)::log))
        simp_rw [inner]
        rw [mean_swap]
        rw [← LawTransport.mean_product (fun pair : (A → OracleAnswer) × OracleAnswer =>
          f ((a,pair.2)::runLog (k pair.2)
            (fun b => cached (Function.update c (key a) (some pair.2)) pair.1 (key b)) q))]
        have hh := mean_update (key a)
          (fun H => f (runLog (.query a k) (fun b => cached c H (key b)) (q+1)))
        rw [← hh]
        apply congrArg mean
        funext pair
        rw [cached_update c pair.1 (key a) pair.2 hc]
        simp only [runLog, cached, Function.update_self, Option.getD_some]

#print axioms lazy_draws
#print axioms mean_update
#print axioms mean_snoc
#print axioms mean_swap
#print axioms cached_update
#print axioms lazy_uniform
end R1Z.SimCostLazyCoupling
