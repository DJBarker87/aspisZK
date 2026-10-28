import R1Z.ProverCommitSeedJoin19
/-! Joint source-coin / adaptive history coupling. Replacing the finite set
of seed coin coordinates preserves the whole table law, and the entire
adaptive history is identical until a seed-namespace query. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitJointHistory19
open R0Z R0Z.FsStatement R0Z.FsAbort R0Z.LawTransport
open R1Z.GamesR1 R1Z.CouplingR1PBin R1Z.ProverCommitSeedEvent19
attribute [local instance] Classical.propDecidable
variable {A I U : Type} [DecidableEq A]

def exchange (X Y : Type) : (X × (X × Y)) ≃ (X × (X × Y)) where
  toFun p := (p.2.1, p.1, p.2.2)
  invFun p := (p.2.1, p.1, p.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

def swapCoordinates (key : I → A) (injective : Function.Injective key) :
    ((I → U) × (A → U)) ≃ ((I → U) × (A → U)) :=
  let split := QueryScanIdealHistory.splitCoordinates (U := U) key injective
  let reshape := Equiv.prodCongr (Equiv.refl (I → U)) split
  reshape.trans ((exchange (I → U) ({a : A // ¬ ∃ i, key i = a} → U)).trans reshape.symm)

def replaceTable (key : I → A) (injective : Function.Injective key)
    (coins : I → U) (table : A → U) : A → U :=
  (swapCoordinates key injective (coins, table)).2

theorem replace_at (key : I → A) (injective : Function.Injective key)
    (coins : I → U) (table : A → U) (i : I) :
    replaceTable key injective coins table (key i) = coins i := by
  change (if hx : ∃ j, key j = key i then coins (Classical.choose hx) else
    table (key i)) = coins i
  rw [dif_pos ⟨i,rfl⟩]
  exact congrArg coins (injective (Classical.choose_spec (show ∃ j, key j = key i from ⟨i,rfl⟩)))

theorem replace_off (key : I → A) (injective : Function.Injective key)
    (coins : I → U) (table : A → U) (a : A) (outside : ¬ ∃ i, key i = a) :
    replaceTable key injective coins table a = table a := by
  change (if hx : ∃ i, key i = a then coins (Classical.choose hx) else table a) = table a
  rw [dif_neg outside]

theorem replacement_uniform [Fintype A] [Fintype I] [Fintype U] [Nonempty U]
    (key : I → A) (injective : Function.Injective key) :
    MP (fun p : (I → U) × (A → U) => replaceTable key injective p.1 p.2) := by
  intro f
  exact (mp_equiv (swapCoordinates (U := U) key injective) (fun p => f p.2)).trans
    (mp_snd f)

/-- Exact adaptive trace transport, including repeats, addresses, order,
answers and early termination. The exception is tested on the model trace. -/
theorem runLog_agrees (program : OProg) (model source : List UInt8 → OracleAnswer)
    (fuel : Nat)
    (off : ∀ e ∈ runLog program model fuel, source e.1 = model e.1) :
    runLog program source fuel = runLog program model fuel := by
  induction fuel generalizing program with
  | zero => cases program <;> rfl
  | succ fuel ih =>
    cases program with
    | done => rfl
    | query a k =>
      have ha := off (a,model a) (by simp only [runLog, List.mem_cons, true_or])
      simp only [runLog, ha]
      congr 1
      exact ih (k (model a)) (fun e he => off e (List.mem_cons_of_mem _ he))

/-- Concrete byte-frame application: all simulator coin entries, for any
bounded finite coordinate schedule, are protected by the single seed event. -/
theorem byte_history_agrees {count : Nat} (room : count ≤ 2^64)
    (bound : Nat) [Fintype (RomFiniteBin.Address bound)] (fits : 65 ≤ bound)
    (seed : OracleAnswer) (coins : ProverCommitSimulatorOracle18.Index count → OracleAnswer)
    (table : RomFiniteBin.Address bound → OracleAnswer) (program : OProg) (fuel : Nat)
    (fresh : ¬ seedGuess (runLog program (RomFiniteBin.lookup bound table) fuel) seed) :
    let key := ProverCommitSimulatorOracle18.key (count := count) bound fits seed
    let hinj := ProverCommitSimulatorOracle18.key_injective room bound fits seed
    runLog program (RomFiniteBin.lookup bound (replaceTable key hinj coins table)) fuel =
      runLog program (RomFiniteBin.lookup bound table) fuel := by
  dsimp only
  apply runLog_agrees
  intro e he
  unfold RomFiniteBin.lookup
  split
  · next a decoded =>
    apply replace_off
    rintro ⟨i, hi⟩
    have hb : a.val = e.1 := by
      have hd := RomFiniteBin.decode_encode bound a
      have hinj := RomFiniteBin.encode_decode bound e.1 a decoded
      exact hinj
    have keyeq := congrArg Subtype.val hi
    have point : seedPoint e.1 seed := by
      rw [← hb, ← keyeq]
      exact source_point seed _ _ _
    exact fresh ⟨e, he, point⟩
  · rfl

/-- Source has one table and a retained seed; the model has independent
coin coordinates, a table, and that same seed. These are exact uniform
marginals, rather than marginal coin uniformity alone. -/
def seededCoupling {S : Type} [Fintype S] [Nonempty S]
    [Fintype A] [Fintype I] [Fintype U] [Nonempty U]
    (key : S → I → A) (injective : ∀ seed, Function.Injective (key seed)) :
    Coupling (S × (A → U)) (((I → U) × (A → U)) × S) where
  S := S × ((I → U) × (A → U))
  finS := inferInstance
  nonemptyS := inferInstance
  toR := fun p => (p.1, replaceTable (key p.1) (injective p.1) p.2.1 p.2.2)
  toM := fun p => (p.2, p.1)
  meanR := by
    intro f
    rw [mean_product, mean_product]
    congr 1
    funext seed
    exact replacement_uniform (key seed) (injective seed) (fun table => f (seed,table))
  meanM := fun f => mp_equiv (Equiv.prodComm S ((I → U) × (A → U))) f

/-- Joint observable equality for arbitrary post-coin views and adaptive
programs on actual finite byte addresses. This includes deterministic
retry/abort projections of this bounded coin array. The remaining unbounded
source loops and source view correspondence are separate obligations. -/
theorem joint_observation {count : Nat} (room : count ≤ 2^64)
    (bound : Nat) [Fintype (RomFiniteBin.Address bound)] (fits : 65 ≤ bound)
    {V : Type} (view : (ProverCommitSimulatorOracle18.Index count → OracleAnswer) → V)
    (program : V → OProg) (fuel : Nat)
    (seed : OracleAnswer) (coins : ProverCommitSimulatorOracle18.Index count → OracleAnswer)
    (table : RomFiniteBin.Address bound → OracleAnswer)
    (fresh : ¬ seedGuess (runLog (program (view coins)) (RomFiniteBin.lookup bound table) fuel) seed) :
    let key := ProverCommitSimulatorOracle18.key (count := count) bound fits seed
    let hinj := ProverCommitSimulatorOracle18.key_injective room bound fits seed
    let sourceTable := replaceTable key hinj coins table
    let sourceCoins := fun i => sourceTable (key i)
    (view sourceCoins, runLog (program (view sourceCoins))
      (RomFiniteBin.lookup bound sourceTable) fuel) =
    (view coins, runLog (program (view coins)) (RomFiniteBin.lookup bound table) fuel) := by
  dsimp only
  have hc : (fun i => replaceTable
      (ProverCommitSimulatorOracle18.key (count := count) bound fits seed)
      (ProverCommitSimulatorOracle18.key_injective room bound fits seed) coins table
      (ProverCommitSimulatorOracle18.key bound fits seed i)) = coins := by
    funext i
    exact replace_at _ _ _ _ i
  rw [hc]
  exact congrArg (fun log => (view coins, log))
    (byte_history_agrees room bound fits seed coins table (program (view coins)) fuel fresh)

/-- Pointwise protection also transports the shipped simulator's programmed
lookup before its shared-oracle fallback. -/
theorem byte_oracle_agrees {count : Nat} (room : count ≤ 2^64)
    (bound : Nat) [Fintype (RomFiniteBin.Address bound)] (fits : 65 ≤ bound)
    (seed : OracleAnswer) (coins : ProverCommitSimulatorOracle18.Index count → OracleAnswer)
    (table : RomFiniteBin.Address bound → OracleAnswer) (a : List UInt8)
    (fresh : ¬ seedPoint a seed) :
    RomFiniteBin.lookup bound (replaceTable
      (ProverCommitSimulatorOracle18.key (count := count) bound fits seed)
      (ProverCommitSimulatorOracle18.key_injective room bound fits seed) coins table) a =
      RomFiniteBin.lookup bound table a := by
  unfold RomFiniteBin.lookup
  split
  · next addr decoded =>
    apply replace_off
    rintro ⟨i, hi⟩
    have hb := RomFiniteBin.encode_decode bound a addr decoded
    have keyeq := congrArg Subtype.val hi
    apply fresh
    rw [← hb, ← keyeq]
    exact source_point seed _ _ _
  · rfl

def programmedOracle (entries : List Entry) (fallback : List UInt8 → OracleAnswer) :
    List UInt8 → OracleAnswer := fun a => (List.lookup a entries).getD (fallback a)

theorem programmed_history_agrees {count : Nat} (room : count ≤ 2^64)
    (bound : Nat) [Fintype (RomFiniteBin.Address bound)] (fits : 65 ≤ bound)
    (seed : OracleAnswer) (coins : ProverCommitSimulatorOracle18.Index count → OracleAnswer)
    (table : RomFiniteBin.Address bound → OracleAnswer) (entries : List Entry)
    (program : OProg) (fuel : Nat)
    (fresh : ¬ seedGuess (runLog program
      (programmedOracle entries (RomFiniteBin.lookup bound table)) fuel) seed) :
    runLog program (programmedOracle entries (RomFiniteBin.lookup bound (replaceTable
      (ProverCommitSimulatorOracle18.key (count := count) bound fits seed)
      (ProverCommitSimulatorOracle18.key_injective room bound fits seed) coins table))) fuel =
      runLog program (programmedOracle entries (RomFiniteBin.lookup bound table)) fuel := by
  apply runLog_agrees
  intro e he
  unfold programmedOracle
  rw [byte_oracle_agrees room bound fits seed coins table e.1
    (fun hp => fresh ⟨e,he,hp⟩)]

/-- Generic whole-component certificate with a pointwise table adapter.
For the source byte namespace, byte_oracle_agrees discharges the adapter. -/
def componentJoin [Fintype A] [Fintype I]
    (key : OracleAnswer → I → A) (injective : ∀ seed, Function.Injective (key seed))
    (lookup : (A → OracleAnswer) → List UInt8 → OracleAnswer)
    (off : ∀ seed coins table a, ¬ seedPoint a seed →
      lookup (replaceTable (key seed) (injective seed) coins table) a = lookup table a)
    {V : Type} (view : (I → OracleAnswer) → V)
    (entries : (I → OracleAnswer) → List Entry)
    (program : V → OProg) (fuel : Nat) :
    let runtime := fun r : OracleAnswer × (A → OracleAnswer) =>
      let c := fun i => r.2 (key r.1 i)
      (view c, runLog (program (view c)) (programmedOracle (entries c) (lookup r.2)) fuel)
    let model := fun m : (I → OracleAnswer) × (A → OracleAnswer) =>
      (view m.1, runLog (program (view m.1)) (programmedOracle (entries m.1) (lookup m.2)) fuel)
    ProverCommitSeedJoin19.RunJoin runtime model (fun _ _ => False)
      (fun m => runLog (program (view m.1)) (programmedOracle (entries m.1) (lookup m.2)) fuel) := by
  dsimp only
  refine ⟨seededCoupling key injective, ?_⟩
  intro p hn
  dsimp only [seededCoupling] at hn ⊢
  have hc : (fun i => replaceTable (key p.1) (injective p.1) p.2.1 p.2.2
      (key p.1 i)) = p.2.1 := by
    funext i
    exact replace_at _ _ _ _ i
  rw [hc]
  apply congrArg (fun log => (view p.2.1,log))
  apply runLog_agrees
  intro e he
  have fresh : ¬ seedPoint e.1 p.1 := by
    intro hp
    exact hn ⟨0,Or.inr ⟨rfl,⟨e,he,hp⟩⟩⟩
  unfold programmedOracle
  rw [off p.1 p.2.1 p.2.2 e.1 fresh]

#print axioms exchange
#print axioms swapCoordinates
#print axioms replace_at
#print axioms replace_off
#print axioms replacement_uniform
#print axioms runLog_agrees
#print axioms byte_history_agrees
#print axioms seededCoupling
#print axioms joint_observation
#print axioms byte_oracle_agrees
#print axioms programmed_history_agrees
#print axioms componentJoin
end R1Z.ProverCommitJointHistory19
