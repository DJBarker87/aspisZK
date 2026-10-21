import R1Z.SimCostLazyCoupling
import R1Z.SimCostRelativeReplay

/-! A list implementation of the byte-key lazy cache. It charges comparisons,
answer writes (32 bytes), query logging and cache insertion. Continuations
remain external oracle-machine work, as in the replay model. -/
set_option autoImplicit false
namespace R1Z.SimCostLazyBytes
open R0Z.FsStatement R1Z.GamesR1 R1Z.SimCostWriter R1Z.SimCostReplay
open R1Z.SimCostLazyCoupling

def run (t : Table) (p : OProg) : (q : Nat) → (Fin q → OracleAnswer) → Costed Table
  | 0, _ => ([],0)
  | q+1, u => match p with
    | .done => ([],0)
    | .query a k =>
      let found := lookup a t
      match found.1 with
      | some v =>
        let r := run t (k v) q (Fin.init u)
        ((a,v)::r.1, found.2+r.2+a.length+33)
      | none =>
        let v := u (Fin.last q)
        let r := run ((a,v)::t) (k v) q (Fin.init u)
        ((a,v)::r.1, found.2+r.2+2*a.length+66)

theorem cons_lookup (t : Table) (a : List UInt8) (v : OracleAnswer) :
    (fun b => ((a,v)::t).lookup b) = Function.update (fun b => t.lookup b) a (some v) := by
  funext b
  by_cases h : b = a
  · subst b; simp
  · simp only [List.lookup, beq_eq_false_iff_ne.mpr h, Function.update_of_ne h]

theorem run_erase (t : Table) (p : OProg) (q : Nat) (u : Fin q → OracleAnswer) :
    (run t p q u).1 = (lazyRun id (fun a => t.lookup a) p q u).1 := by
  induction q generalizing t p with
  | zero => cases p <;> rfl
  | succ q ih =>
    cases p with
    | done => rfl
    | query a k =>
      simp only [run, lookup_erase, lazyRun, id_eq]
      cases h : t.lookup a with
      | none => simp only [ih, cons_lookup]
      | some v => exact congrArg (List.cons (a,v)) (ih t (k v) (Fin.init u))

/-- Every reached address is bounded by L, including fresh cache keys. -/
def Addresses (L : Nat) (t : Table) (p : OProg) :
    (q : Nat) → (Fin q → OracleAnswer) → Prop
  | 0, _ => True
  | q+1, u => match p with
    | .done => True
    | .query a k => a.length ≤ L ∧
      match t.lookup a with
      | some v => Addresses L t (k v) q (Fin.init u)
      | none => Addresses L ((a,u (Fin.last q))::t) (k (u (Fin.last q))) q (Fin.init u)

theorem run_bound (t : Table) (p : OProg) (q L : Nat) (u : Fin q → OracleAnswer)
    (ht : KeysBound L t) (hp : Addresses L t p q u) :
    (run t p q u).2 ≤ q*((t.length+q+1)*(2*L+3)+2*L+66) := by
  induction q generalizing t p with
  | zero => simp only [run]; omega
  | succ q ih =>
    cases p with
    | done => simp only [run]; positivity
    | query a k =>
      simp only [Addresses] at hp
      obtain ⟨ha,hp⟩ := hp
      have hb := lookup_bound a t L ha ht
      simp only [run, lookup_erase]
      cases h : t.lookup a with
      | some v =>
        have hr := ih t (k v) (Fin.init u) ht (by simpa only [h] using hp)
        simp only
        nlinarith
      | none =>
        have ht' : KeysBound L ((a,u (Fin.last q))::t) := by
          intro b v hm
          rcases List.mem_cons.mp hm with he | he
          · cases he; exact ha
          · exact ht b v he
        have hr := ih _ (k (u (Fin.last q))) (Fin.init u) ht' (by simpa only [h] using hp)
        simp only [List.length_cons] at hr
        simp only
        nlinarith


def bytes (t : Table) : Nat := (t.map (fun row => row.1.length)).sum

theorem addresses_mono (t : Table) (p : OProg) (q L M : Nat)
    (u : Fin q → OracleAnswer) (h : L ≤ M) (hp : Addresses L t p q u) :
    Addresses M t p q u := by
  induction q generalizing t p with
  | zero => cases p <;> trivial
  | succ q ih =>
    cases p with
    | done => trivial
    | query a k =>
      simp only [Addresses] at hp ⊢
      refine ⟨hp.1.trans h, ?_⟩
      cases he : t.lookup a with
      | none => exact ih _ _ (Fin.init u) (by simpa only [he] using hp.2)
      | some v => exact ih _ _ (Fin.init u) (by simpa only [he] using hp.2)

theorem addresses_bytes (t : Table) (p : OProg) (q : Nat)
    (u : Fin q → OracleAnswer) : Addresses (bytes (run t p q u).1) t p q u := by
  induction q generalizing t p with
  | zero => cases p <;> trivial
  | succ q ih =>
    cases p with
    | done => trivial
    | query a k =>
      simp only [run, lookup_erase, Addresses]
      cases he : t.lookup a with
      | some v =>
        have hr := ih t (k v) (Fin.init u)
        change a.length ≤ a.length + bytes (run t (k v) q (Fin.init u)).1 ∧ _
        exact ⟨Nat.le_add_right _ _, addresses_mono _ _ _ _ _ _ (Nat.le_add_left _ _) hr⟩
      | none =>
        have hr := ih ((a,u (Fin.last q))::t) (k (u (Fin.last q))) (Fin.init u)
        change a.length ≤ a.length + bytes (run _ _ _ _).1 ∧ _
        exact ⟨Nat.le_add_right _ _, addresses_mono _ _ _ _ _ _ (Nat.le_add_left _ _) hr⟩

/-- A conservative cubic byte-work bound; no bound on adversary key lengths.
The relative input n is the query cap plus bytes actually reached by this
lazy run. The initial programmed table remains a fixed protocol constant. -/
theorem run_relative (t : Table) (p : OProg) (q L : Nat)
    (u : Fin q → OracleAnswer) (ht : KeysBound L t) :
    let n := q + bytes (run t p q u).1
    (run t p q u).2 ≤ (t.length+2)*(2*L+69)*(n+1)^3 := by
  let b := bytes (run t p q u).1
  let n := q+b
  have ht' : KeysBound (L+b) t := fun a v hm => (ht a v hm).trans (Nat.le_add_right _ _)
  have ha := addresses_mono t p q b (L+b) u (Nat.le_add_left _ _) (addresses_bytes t p q u)
  have hb := run_bound t p q (L+b) u ht' ha
  have hq : q ≤ n+1 := by dsimp [n]; omega
  have hl : t.length+q+2 ≤ (t.length+2)*(n+1) := by dsimp [n]; nlinarith
  have hw : 2*(L+b)+69 ≤ (2*L+69)*(n+1) := by dsimp [n]; nlinarith
  have hs : q*((t.length+q+1)*(2*(L+b)+3)+2*(L+b)+66) ≤
      q*((t.length+q+2)*(2*(L+b)+69)) := by nlinarith
  have hm := Nat.mul_le_mul hq (Nat.mul_le_mul hl hw)
  change (run t p q u).2 ≤ (t.length+2)*(2*L+69)*(n+1)^3
  exact hb.trans (hs.trans (hm.trans_eq (by ring)))

#print axioms addresses_mono
#print axioms addresses_bytes
#print axioms run_relative
#print axioms cons_lookup
#print axioms run_erase
#print axioms run_bound
end R1Z.SimCostLazyBytes
