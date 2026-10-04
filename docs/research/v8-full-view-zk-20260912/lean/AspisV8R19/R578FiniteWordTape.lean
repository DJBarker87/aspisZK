import AspisV8R19.R572SequentialWordMass

set_option autoImplicit false
namespace AspisV8R19.R578FiniteWordTape
open MemoizedProgramLaw OracleProgramOps AdaptiveFirstReadLaw OracleResampling
open R443BoundedRejectionMass R572SequentialWordMass
variable {p : Nat} {I O R : Type}
noncomputable section

def Bounded : Nat → Program I (Option (Fin p)) O → Prop
  | _, .done _ => True
  | 0, .ask _ _ => False
  | n+1, .ask _ next => ∀ a, Bounded n (next a)

def runTape : (n : Nat) → Program I (Option (Fin p)) O →
    Tape p n → Option (View I (Option (Fin p)) O)
  | _, .done o, _ => some ([],o)
  | 0, .ask _ _, _ => none
  | n+1, .ask i next, t =>
      (runTape n (next (t 0)) (fun j => t j.succ)).map
        (fun v => ((i,t 0)::v.1,v.2))

def observeTape (observe : View I (Option (Fin p)) O → ℚ)
    (v : Option (View I (Option (Fin p)) O)) : ℚ :=
  match v with
  | none => 0
  | some v => observe v

theorem tape_mean (n : Nat) (program : Program I (Option (Fin p)) O)
    (hb : Bounded n program) (observe : View I (Option (Fin p)) O → ℚ) :
    mean (fun t : Tape p n => observeTape observe (runTape n program t)) =
      independentMean program observe := by
  induction n generalizing program observe with
  | zero =>
      cases program with
      | done o => exact mean_const _
      | ask i next => exact False.elim hb
  | succ n ih =>
      cases program with
      | done o => exact mean_const _
      | ask i next =>
          rw [← mean_equiv (splitTape p n).symm
            (fun t : Tape p (n+1) => observeTape observe (runTape (n+1) (.ask i next) t))]
          change mean (fun q : Option (Fin p) × Tape p n =>
            observeTape observe ((runTape n (next q.1) q.2).map
              (fun v => ((i,q.1)::v.1,v.2)))) = _
          rw [mean_prod (fun (a : Option (Fin p)) (t : Tape p n) =>
            observeTape observe ((runTape n (next a) t).map
              (fun v => ((i,a)::v.1,v.2))))]
          change mean (fun a : Option (Fin p) =>
            mean (fun t : Tape p n => observeTape observe
              ((runTape n (next a) t).map (fun v => ((i,a)::v.1,v.2))))) = _
          change _ = mean (fun a => independentMean (next a)
            (fun v => observe ((i,a)::v.1,v.2)))
          apply mean_congr
          intro a
          have hpoint : ∀ t : Tape p n,
              observeTape observe ((runTape n (next a) t).map
                (fun v => ((i,a)::v.1,v.2))) =
              observeTape (fun v => observe ((i,a)::v.1,v.2))
                (runTape n (next a) t) := by
            intro t
            cases runTape n (next a) t <;> rfl
          rw [mean_congr hpoint]
          exact ih (next a) (hb a) _

theorem runTape_success (n : Nat) (program : Program I (Option (Fin p)) O)
    (hb : Bounded n program) (t : Tape p n) :
    ∃ v, runTape n program t = some v := by
  induction n generalizing program with
  | zero =>
      cases program with
      | done o => exact ⟨([],o), rfl⟩
      | ask i next => exact False.elim hb
  | succ n ih =>
      cases program with
      | done o => exact ⟨([],o), rfl⟩
      | ask i next =>
          obtain ⟨v,hv⟩ := ih (next (t 0)) (hb (t 0)) (fun j => t j.succ)
          exact ⟨((i,t 0)::v.1,v.2), by simp only [runTape, hv, Option.map_some]⟩

theorem bounded_mono (n m : Nat) (program : Program I (Option (Fin p)) O)
    (hb : Bounded n program) : Bounded (n+m) program := by
  induction n generalizing program with
  | zero => cases program <;> simp_all [Bounded]
  | succ n ih =>
      cases program with
      | done o => simp only [Bounded]
      | ask i next =>
          rw [show n+1+m=(n+m)+1 by omega]
          change ∀ a, Bounded (n+m) (next a)
          exact fun a => ih (next a) (hb a)

theorem bounded_bind (n m : Nat) (program : Program I (Option (Fin p)) O)
    (next : O → Program I (Option (Fin p)) R)
    (hb : Bounded n program) (hk : ∀ o, Bounded m (next o)) :
    Bounded (n+m) (bind program next) := by
  induction n generalizing program with
  | zero =>
      cases program with
      | done o => simpa only [Nat.zero_add, OracleProgramOps.bind] using hk o
      | ask i k => exact False.elim hb
  | succ n ih =>
      cases program with
      | done o =>
          have h := bounded_mono m (n+1) (next o) (hk o)
          simpa only [OracleProgramOps.bind, Nat.add_comm] using h
      | ask i k =>
          rw [show n+1+m=(n+m)+1 by omega]
          change ∀ a, Bounded (n+m) (bind (k a) next)
          exact fun a => ih (k a) (hb a)

theorem scan_bounded (n cursor : Nat) : Bounded n (scan (p := p) n cursor) := by
  induction n generalizing cursor with
  | zero => trivial
  | succ n ih =>
      change ∀ a : Option (Fin p), Bounded n _
      intro a
      cases a with
      | none => exact ih _
      | some a => simp only [Bounded]

theorem limbs_bounded (budget count cursor : Nat) :
    Bounded (budget*count) (limbs (p := p) budget count cursor) := by
  induction count generalizing cursor with
  | zero => trivial
  | succ count ih =>
      rw [Nat.mul_succ, Nat.add_comm]
      apply bounded_bind budget (budget*count) _ _ (scan_bounded budget cursor)
      intro first
      cases first.1 with
      | none => simp only [Bounded]
      | some a =>
          have h := bounded_bind (budget*count) 0
            (limbs (p := p) budget count first.2)
            (fun tail => .done (prependResult a tail)) (ih first.2) (fun _ => by simp only [Bounded])
          simpa only [Nat.add_zero] using h

theorem finite_tuple_mass (hp : 0 < p) (budget count cursor : Nat)
    (target : Fin count → Fin p) :
    mean (fun t : Tape p (budget*count) =>
      observeTape (observedList (List.ofFn target))
        (runTape (budget*count) (limbs budget count cursor) t)) =
      ((1-(1/(p+1 : ℚ))^budget)/p)^count := by
  rw [tape_mean _ _ (limbs_bounded budget count cursor)]
  exact limbs_exact_mass hp budget count cursor target

#print axioms runTape_success
#print axioms bounded_mono
#print axioms tape_mean
#print axioms bounded_bind
#print axioms scan_bounded
#print axioms limbs_bounded
#print axioms finite_tuple_mass
end
end AspisV8R19.R578FiniteWordTape
