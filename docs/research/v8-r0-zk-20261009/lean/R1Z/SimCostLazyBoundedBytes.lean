import R1Z.SimCostLazyBytes
import R1Z.SimCostLazyProtocol

/-! Byte-work implementation of the bounded ROM cache. Long addresses are
scanned and answered zero; they are never inserted. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.SimCostLazyBoundedBytes
open R0Z R0Z.FsStatement R0Z.FsAbortBounds R1Z.GamesR1
open R1Z.SimCostWriter R1Z.SimCostReplay R1Z.SimCostLazyCoupling R1Z.SimCostLazyProtocol
attribute [local instance] Classical.propDecidable

def run (w : Nat) (t : Table) (p : OProg) :
    (q : Nat) → (Fin q → OracleAnswer) → Costed Table
  | 0, _ => ([],0)
  | q+1, u => match p with
    | .done => ([],0)
    | .query a k =>
      if a.length ≤ w then
        let found := SimCostReplay.lookup a t
        match found.1 with
        | some v =>
          let r := run w t (k v) q (Fin.init u)
          ((a,v)::r.1,found.2+r.2+3*a.length+67)
        | none =>
          let v := u (Fin.last q)
          let r := run w ((a,v)::t) (k v) q (Fin.init u)
          ((a,v)::r.1,found.2+r.2+3*a.length+67)
      else
        let r := run w t (k 0) q (Fin.init u)
        ((a,0)::r.1,r.2+a.length+33)

theorem initial_cons (w : Nat) (t : Table) (a : List UInt8) (v : OracleAnswer)
    (ha : a.length ≤ w) :
    initial w ((a,v)::t) =
      Function.update (initial w t) (RomFiniteBin.decode w a) (some v) := by
  have hd := (RomFiniteBin.decode_isSome w a).mpr ha
  cases he : RomFiniteBin.decode w a with
  | none => simp only [he, Option.isSome_none, Bool.false_eq_true] at hd
  | some x =>
    have hx := RomFiniteBin.encode_decode w a x he
    funext b
    cases b with
    | none =>
      rw [Function.update_of_ne (show (none : Option (RomFiniteBin.Address w)) ≠ some x from by simp)]
      rfl
    | some y =>
      by_cases hy : y = x
      · subst y; simp [initial, hx]
      · have hn : y.val ≠ a := by
          intro hh
          apply hy
          apply Subtype.ext
          exact hh.trans hx.symm
        rw [Function.update_of_ne (show (some y : Option (RomFiniteBin.Address w)) ≠ some x from by simpa using hy)]
        simp only [initial, List.lookup, beq_eq_false_iff_ne.mpr hn]

theorem run_erase (w : Nat) (t : Table) (p : OProg) (q : Nat)
    (u : Fin q → OracleAnswer) :
    (run w t p q u).1 =
      (lazyRun (RomFiniteBin.decode w) (initial w t) p q u).1 := by
  induction q generalizing t p with
  | zero => cases p <;> rfl
  | succ q ih =>
    cases p with
    | done => rfl
    | query a k =>
      by_cases ha : a.length ≤ w
      · have hd := (RomFiniteBin.decode_isSome w a).mpr ha
        cases he : RomFiniteBin.decode w a with
        | none => simp only [he, Option.isSome_none, Bool.false_eq_true] at hd
        | some x =>
          have hx := RomFiniteBin.encode_decode w a x he
          simp only [run, if_pos ha, lookup_erase, lazyRun, he, initial, hx]
          cases hh : t.lookup a with
          | some v => exact congrArg (List.cons (a,v)) (ih t (k v) (Fin.init u))
          | none =>
            rw [ih, initial_cons w t a _ ha, he]
      · have hd : RomFiniteBin.decode w a = none := by
          cases he : RomFiniteBin.decode w a with
          | none => rfl
          | some x =>
            have hh := (RomFiniteBin.decode_isSome w a).mp (by simp only [he, Option.isSome_some])
            exact False.elim (ha hh)
        simp only [run, if_neg ha, lazyRun, hd, initial]
        exact congrArg (List.cons (a,0)) (ih t (k 0) (Fin.init u))

theorem run_bound (w : Nat) (t : Table) (p : OProg) (q : Nat)
    (u : Fin q → OracleAnswer) (ht : KeysBound w t) :
    (run w t p q u).2 ≤
      q*((t.length+q+1)*(2*w+3)+3*w+67) + SimCostLazyBytes.bytes (run w t p q u).1 := by
  induction q generalizing t p with
  | zero => simp only [run, SimCostLazyBytes.bytes, List.map_nil, List.sum_nil]; omega
  | succ q ih =>
    cases p with
    | done => simp only [run, SimCostLazyBytes.bytes, List.map_nil, List.sum_nil]; positivity
    | query a k =>
      by_cases ha : a.length ≤ w
      · have hb := lookup_bound a t w ha ht
        simp only [run, if_pos ha, lookup_erase]
        cases hh : t.lookup a with
        | some v =>
          have hr := ih t (k v) (Fin.init u) ht
          change _ ≤ _ + (a.length + SimCostLazyBytes.bytes (run w t (k v) q (Fin.init u)).1)
          nlinarith
        | none =>
          have ht' : KeysBound w ((a,u (Fin.last q))::t) := by
            intro b v hm
            rcases List.mem_cons.mp hm with he | he
            · cases he; exact ha
            · exact ht b v he
          have hr := ih _ (k (u (Fin.last q))) (Fin.init u) ht'
          simp only [List.length_cons] at hr
          change _ ≤ _ + (a.length + SimCostLazyBytes.bytes (run w _ _ _ _).1)
          nlinarith
      · have hr := ih t (k 0) (Fin.init u) ht
        simp only [run, if_neg ha]
        change _ ≤ _ + (a.length + SimCostLazyBytes.bytes (run w t (k 0) q (Fin.init u)).1)
        nlinarith


/-- Relative quadratic bound, including scans of out-of-domain queries. -/
theorem run_relative (w : Nat) (t : Table) (p : OProg) (q : Nat)
    (u : Fin q → OracleAnswer) (ht : KeysBound w t) :
    let n := q + SimCostLazyBytes.bytes (run w t p q u).1
    (run w t p q u).2 ≤ ((t.length+2)*(5*w+70)+1)*(n+1)^2 := by
  let b := SimCostLazyBytes.bytes (run w t p q u).1
  let n := q+b
  have hb := run_bound w t p q u ht
  have hs : q*((t.length+q+1)*(2*w+3)+3*w+67) ≤
      q*((t.length+q+2)*(5*w+70)) := by
    apply Nat.mul_le_mul_left
    nlinarith
  have hq : q ≤ n+1 := by dsimp [n]; omega
  have hl : t.length+q+2 ≤ (t.length+2)*(n+1) := by dsimp [n]; nlinarith
  have hm := Nat.mul_le_mul hq (Nat.mul_le_mul_right (5*w+70) hl)
  have he : (n+1)*((t.length+2)*(n+1)*(5*w+70)) =
      ((t.length+2)*(5*w+70))*(n+1)^2 := by ring
  rw [he] at hm
  have hbn : b ≤ (n+1)^2 := by dsimp [n]; nlinarith
  change (run w t p q u).2 ≤ ((t.length+2)*(5*w+70)+1)*(n+1)^2
  change (run w t p q u).2 ≤ _ + b at hb
  nlinarith

/-- The implemented cache has exactly the existing bounded-ROM law. -/
theorem uniform (w : Nat) (t : Table) (ht : KeysBound w t)
    (p : OProg) (q : Nat) (f : Table → ℚ) :
    mean (fun u : Fin q → OracleAnswer => f (t ++ (run w t p q u).1)) =
      mean (fun H : RomFiniteBin.Address w → OracleAnswer =>
        f (t ++ runLog p (fun a => (t.lookup a).getD (RomFiniteBin.lookup w H a)) q)) := by
  simp_rw [run_erase]
  exact bounded_lazy_uniform w t ht p q f


section Protocol
open R0P R0Z.JointView R1Z.Batched R1Z.GamesR1PBin R1Z.SimCostIdeal
local notation "K" => PrivacyR1AcctBasis.K
local notation "F" => PrivacyR1AcctBasis.F
local notation "B" => PrivacyR1AcctBasis.basis
variable {CommitHandle Aux : Type}
variable (template : R1Wire K CommitHandle Aux) (input : HonestProver K)
  (outputs : Statement K CommitHandle → Challenges K → Aux)
  (x : Statement K CommitHandle)
local notation "base" => PrivacyR1AcctModel.base template PhaseWireLog2Bin.log
local notation "W" => PhaseLocalityBin.R1PhaseWire.toWire
  (PhaseProtocolInstanceBin.wire base (List.length (R1Wire.pubBytes base x))
    (PhaseWireLog2Bin.honest input) B outputs x)
local notation "width" => RomGrammarBin.bound (List.length (R1Wire.pubBytes base x))
local notation "T" => TranscriptR1.schedule.length + 2*Fintype.card (Fin 3 ⊕ RIdx)

/-- The protocol's actual prepared table supplies both size contracts. This
cost conclusion has no preparation-stage or adversary-address premise. -/
theorem protocol_relative (P : Challenges K → Prop)
    (sim : Challenges K → Tape K F → View K CommitHandle Aux R1Bat)
    (adv : R1Adv K CommitHandle Aux)
    (r : (Fin 8 → R1Coins (W).Cm (W).Tab) × (Fin 8 → Tape K F))
    (u : Fin (W).qmax → OracleAnswer) :
    let s := prepare W 8 (by decide) P x sim r
    let result := run width s.table (adv.prog s.view s.table) (W).qmax u
    result.2 ≤ ((T+2)*(5*width+70)+1)*
      ((W).qmax + SimCostLazyBytes.bytes result.1 + 1)^2 := by
  let s := prepare W 8 (by decide) P x sim r
  have ht := SimCostProtocolStoredSizes.preparation_stored_sizes template input outputs x P sim r
  have hb := run_relative width s.table (adv.prog s.view s.table) (W).qmax u ht.2
  have hc : (s.table.length+2)*(5*width+70)+1 ≤ (T+2)*(5*width+70)+1 := by
    have hm := Nat.mul_le_mul_right (5*width+70) (Nat.add_le_add_right ht.1 2)
    exact Nat.add_le_add_right hm 1
  exact hb.trans (Nat.mul_le_mul_right _ hc)

/-- Fixed-preparation observer law for the same costed protocol replay.
Joint preparation-source independence remains outside this theorem. -/
theorem protocol_uniform (P : Challenges K → Prop)
    (sim : Challenges K → Tape K F → View K CommitHandle Aux R1Bat)
    (adv : R1Adv K CommitHandle Aux)
    (r : (Fin 8 → R1Coins (W).Cm (W).Tab) × (Fin 8 → Tape K F))
    (f : Table → ℚ) :
    let s := prepare W 8 (by decide) P x sim r
    mean (fun u : Fin (W).qmax → OracleAnswer =>
      f (s.table ++ (run width s.table (adv.prog s.view s.table) (W).qmax u).1)) =
      mean (fun H : RomFiniteBin.Address width → OracleAnswer =>
        f (s.table ++ runLog (adv.prog s.view s.table)
          (fun a => (s.table.lookup a).getD (RomFiniteBin.lookup width H a)) (W).qmax)) := by
  exact uniform width _
    (SimCostProtocolStoredSizes.preparation_stored_sizes template input outputs x P sim r).2 _ _ f
end Protocol

#print axioms protocol_relative
#print axioms protocol_uniform
#print axioms run_relative
#print axioms uniform
#print axioms initial_cons
#print axioms run_erase
#print axioms run_bound
end R1Z.SimCostLazyBoundedBytes
