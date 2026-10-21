import R1Z.SimCostLazyCoupling
import R1Z.SimCostProtocolStoredSizes

/-! Lazy ROM specialization to the bounded-byte domain in the headline.
This is equality of laws for replay at each fixed programmed state, with a
fresh independent fallback ROM. It does not silently replace or truncate the
field-mask coordinates of ideal preparation. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.SimCostLazyProtocol
open R0P R0Z R0Z.JointView R0Z.FsStatement R0Z.FsAbortBounds R1Z.Batched
  R1Z.GamesR1 R1Z.GamesR1PBin R1Z.SimCostIdeal R1Z.SimCostReplay
  R1Z.SimCostLazyCoupling
attribute [local instance] Classical.propDecidable

/-- Split off the unused out-of-domain coordinate, symbolically. -/
def splitOption {A U : Type} : (Option A → U) ≃ U × (A → U) where
  toFun H := (H none, fun a => H (some a))
  invFun p := fun a => match a with | none => p.1 | some a => p.2 a
  left_inv H := by funext a; cases a <;> rfl
  right_inv p := by cases p; rfl

theorem mean_some {A U : Type} [DecidableEq A] [Fintype A] [Fintype U] [Nonempty U]
    (f : (A → U) → ℚ) :
    mean (fun H : Option A → U => f (fun a => H (some a))) = mean f := by
  rw [mean_equiv' (splitOption (A := A) (U := U)), LawTransport.mean_product]
  change mean (fun _ : U => mean f) = mean f
  exact mean_const' _

/-- Keep the domain abstract while transporting a lazy source law. -/
theorem lazy_projection {A : Type} [DecidableEq A] [Fintype A]
    (key : List UInt8 → Option A) (c : Option A → Option OracleAnswer)
    (p : OProg) (q : Nat) (f : Table → ℚ)
    (O : (A → OracleAnswer) → List UInt8 → OracleAnswer)
    (hO : ∀ H bs, cached c H (key bs) = O (fun a => H (some a)) bs) :
    mean (fun u : Fin q → OracleAnswer => f (lazyRun key c p q u).1) =
      mean (fun H : A → OracleAnswer => f (runLog p (O H) q)) := by
  rw [lazy_uniform key c p q f]
  simp_rw [hO]
  exact mean_some (A := A) (U := OracleAnswer) (fun H => f (runLog p (O H) q))

/-- Out-of-domain addresses return zero. Programmed in-domain keys retain
first-match lookup priority, including any duplicate stored keys. -/
def initial (bound : Nat) (t : Table) : Option (RomFiniteBin.Address bound) → Option OracleAnswer
  | none => some 0
  | some a => t.lookup a.val

theorem outside_lookup (bound : Nat) (t : Table) (bs : List UInt8)
    (ht : KeysBound bound t) (hd : RomFiniteBin.decode bound bs = none) :
    t.lookup bs = none := by
  have hlong : ¬ bs.length ≤ bound := by
    intro hlen
    have hh := (RomFiniteBin.decode_isSome bound bs).mpr hlen
    rw [hd] at hh
    contradiction
  induction t with
  | nil => rfl
  | cons row t ih =>
    rcases row with ⟨a,v⟩
    have ha := ht a v List.mem_cons_self
    have hn : bs ≠ a := by intro he; rw [he] at hlong; exact hlong ha
    have hi := ih (fun b w hb => ht b w (List.mem_cons_of_mem _ hb))
    simp only [List.lookup, beq_eq_false_iff_ne.mpr hn, hi]

theorem initial_oracle (bound : Nat) (t : Table) (ht : KeysBound bound t)
    (H : Option (RomFiniteBin.Address bound) → OracleAnswer) (bs : List UInt8) :
    cached (initial bound t) H (RomFiniteBin.decode bound bs) =
      (t.lookup bs).getD (RomFiniteBin.lookup bound (fun a => H (some a)) bs) := by
  cases hd : RomFiniteBin.decode bound bs with
  | none =>
    rw [outside_lookup bound t bs ht hd]
    simp only [cached, initial, RomFiniteBin.lookup, hd, Option.getD_some, Option.getD_none]
  | some a =>
    have he := RomFiniteBin.encode_decode bound bs a hd
    simp only [cached, initial, RomFiniteBin.lookup, hd]
    rw [he]

/-- Exact bounded-byte ROM source law, with no enumeration of its domain.
The LHS streams independent 256-bit answers, caches at most q new cells and
never allocates the full mathematical table on the RHS. -/
theorem bounded_lazy_uniform (bound : Nat) (t : Table) (ht : KeysBound bound t)
    (p : OProg) (q : Nat) (f : Table → ℚ) :
    mean (fun u : Fin q → OracleAnswer =>
      f (t ++ (lazyRun (RomFiniteBin.decode bound) (initial bound t) p q u).1)) =
    mean (fun H : RomFiniteBin.Address bound → OracleAnswer =>
      f (t ++ runLog p (fun bs => (t.lookup bs).getD (RomFiniteBin.lookup bound H bs)) q)) := by
  exact lazy_projection (RomFiniteBin.decode bound) (initial bound t) p q
    (fun log => f (t ++ log))
    (fun H bs => (t.lookup bs).getD (RomFiniteBin.lookup bound H bs))
    (initial_oracle bound t ht)

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

/-- Protocol-instance specialization, for its actual selected preparation
value. The fallback on the RHS is newly uniform; the joint preparation-source
independence and binary field-tape refinement are separate obligations. -/
theorem protocol_lazy_uniform (P : Challenges K → Prop)
    (sim : Challenges K → Tape K F → View K CommitHandle Aux R1Bat)
    (adv : R1Adv K CommitHandle Aux)
    (r : (Fin 8 → R1Coins (W).Cm (W).Tab) × (Fin 8 → Tape K F))
    (f : Table → ℚ) :
    let s := prepare W 8 (by decide) P x sim r
    mean (fun u : Fin (W).qmax → OracleAnswer =>
      f (s.table ++ (lazyRun (RomFiniteBin.decode width) (initial width s.table)
        (adv.prog s.view s.table) (W).qmax u).1)) =
    mean (fun H : RomFiniteBin.Address width → OracleAnswer =>
      f (s.table ++ runLog (adv.prog s.view s.table)
        (fun bs => (s.table.lookup bs).getD (RomFiniteBin.lookup width H bs)) (W).qmax)) := by
  exact bounded_lazy_uniform width _
    (SimCostProtocolStoredSizes.preparation_stored_sizes template input outputs x P sim r).2 _ _ f

#print axioms splitOption
#print axioms mean_some
#print axioms lazy_projection
#print axioms outside_lookup
#print axioms initial_oracle
#print axioms bounded_lazy_uniform
#print axioms protocol_lazy_uniform
end R1Z.SimCostLazyProtocol
