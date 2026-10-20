import RRActualFieldEnvelopeM10

/-! A work counter on the actual RR states/cursors. Node charges use every
actual scalar call and every eagerly formed normalized child; terminal scans
and successful candidate-prefix copies are included. Reachability supplies
the single uniform stored-row cap, without restricting failed tapes. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.RRActualTraversalWorkM10
open CompPoly RRConcreteState RRConcreteValidState RRActualScalarTraceM10
open RRReachableStorageM10
open AspisV8R19.MemoizedProgramLaw SequentialFreshProgram SequentialProgramInvariants
variable {K : Type} [Field K] [BEq K] [LawfulBEq K] [DecidableEq K] [Fintype K]

def walkWork {S : Type} (run : S → Nat → Result K) (work : S → Nat → Nat) :
    List (K × S) → Nat → Nat
  | [],_ => 1
  | (_,s)::xs,c =>
    let r := run s c
    match r.1.1 with
    | none => work s c+1
    | some ys => work s c+walkWork run work xs r.1.2+2*ys.length+3

theorem walk_bound {S : Type} (run : S → Nat → Result K) (work : S → Nat → Nat)
    (P : S → Prop) (R N : Nat)
    (hw : ∀ s c, P s → work s c ≤ R)
    (hl : ∀ s c, ((run s c).1.1.getD []).length ≤ N)
    (xs : List (K × S)) (hp : ∀ x ∈ xs, P x.2) (c : Nat) :
    walkWork run work xs c ≤ xs.length*(R+2*N+4)+1 := by
  induction xs generalizing c with
  | nil => simp only [walkWork,List.length_nil,Nat.zero_mul,Nat.zero_add,Nat.le_refl]
  | cons x xs ih =>
    rcases x with ⟨a,s⟩
    have hh := hw s c (hp _ List.mem_cons_self)
    have ht := ih (fun x hx => hp x (List.mem_cons_of_mem _ hx)) (run s c).1.2
    have hy := hl s c
    simp only [walkWork]
    split
    · simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
    · rename_i ys hs
      simp only [hs,Option.getD_some] at hy
      simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
      omega

theorem candidates (ell q t d : Nat) (s : ValidState ell K)
    (H : Nat → Fin t → K × K) (c : Nat) (hq : q = Fintype.card K) :
    ((collect ell q t H d s c).1.1.getD []).length ≤ RRTraversalWriterM10.count ell d := by
  let p := RRConcreteWriterM10.run ell q t 0 0 d s
  have hb := all_eval H _ _ (all_sequential p _ (RRConcreteWriterM10.run_bound ell q t 0 0 d s hq) c)
  have hv := ExtractorProgramWorkM10.eval_value H p c
  rw [RRConcreteWriterM10.erase_run] at hv
  have he := (RRActualScalarTraceM10.value ell q t H d s c).trans hv
  have he' := congrArg Prod.fst he
  rw [he']
  exact hb.1

def terminal (D : Nat) (s : RawState K) : Nat :=
  10*(s.maxX+1)*(s.rows.length+1)+10*(s.maxX+1)+10

def terminalBudget (D : Nat) : Nat := 100*(D+2)^2

theorem terminal_bound (D : Nat) (s : RawState K) (h : BoundedRows D s) :
    terminal D s ≤ terminalBudget D := by
  have hx := h.1
  have hm : s.maxX+1 ≤ D+1 := by omega
  have hr : s.rows.length+1 ≤ D+2 := by have hh := h.2.1; omega
  have hp := Nat.mul_le_mul (Nat.mul_le_mul_left 10 hm) hr
  have hq := Nat.mul_le_mul_left 10 hm
  unfold terminal terminalBudget
  nlinarith

def work (D ell q t : Nat) (H : Nat → Fin t → K × K) :
    Nat → ValidState ell K → Nat → Nat
  | 0,s,_ => terminal D s.val
  | d+1,s,c =>
    let r := children ell q t H s c
    let cost := RRActualFieldEnvelopeM10.node D ell q t s H c
    match r.1.1 with
    | none => cost+1
    | some cs => cost+walkWork (collect ell q t H d) (work D ell q t H d) cs r.1.2

theorem children_reachable (ell q t : Nat) (H : Nat → Fin t → K × K)
    (start : RawState K) {n : Nat} (s : ValidState ell K)
    (hr : Reachable ell start n s.val) (c : Nat)
    (cs : List (K × ValidState ell K)) (hs : (children ell q t H s c).1.1 = some cs) :
    ∀ x ∈ cs, Reachable ell start (n+1) x.2.val := by
  unfold children at hs
  cases ho : (GSScalarAtCursorM10.general (scalarPolynomial s.val) q t H c).1.1 with
  | none => simp only [ho,Option.map_none,reduceCtorEq] at hs
  | some roots =>
    simp only [ho,Option.map_some,Option.some.injEq] at hs
    rw [← hs]
    intro x hx
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hx
    exact Reachable.next hr a

theorem work_bound (ell D limit q t : Nat) (start : RawState K)
    (hb : BoundedRows D start) (H : Nat → Fin t → K × K)
    (hq : q = Fintype.card K) (hell : 1 ≤ ell)
    (d : Nat) {n : Nat} (s : ValidState ell K)
    (hr : Reachable ell start n s.val) (hnd : n+d ≤ limit) :
    work (D+(limit+1)*(ell+1)+1) ell q t H d s 0 ≤
      RRTraversalWriterM10.budget ell
        (RRNodeTariffM10.tariff (D+(limit+1)*(ell+1)+1) ell q t)
        (terminalBudget (D+(limit+1)*(ell+1)+1)) d := by
  suffices hall : ∀ c,
      work (D+(limit+1)*(ell+1)+1) ell q t H d s c ≤
        RRTraversalWriterM10.budget ell
          (RRNodeTariffM10.tariff (D+(limit+1)*(ell+1)+1) ell q t)
          (terminalBudget (D+(limit+1)*(ell+1)+1)) d from hall 0
  induction d generalizing n s with
  | zero =>
    intro c
    apply terminal_bound
    apply bounded_mono _ _ _ (reachable_bound ell D start hb hr)
    have hm := Nat.mul_le_mul_right (ell+1) (show n ≤ limit+1 by omega)
    omega
  | succ d ih =>
    intro c
    have hn : n ≤ limit := by omega
    have hc := RRActualFieldEnvelopeM10.reachable_node ell D limit q t start hb s hr hn H c hq hell
    have hl := RRActualScalarTraceBoundsM10.child_length ell q t H s c hq
    simp only [work,RRTraversalWriterM10.budget]
    split
    · omega
    · rename_i cs hs
      have hcs : cs.length ≤ ell := by simpa only [hs,Option.getD_some] using hl
      have hp := children_reachable ell q t H start s hr c cs hs
      have hw := walk_bound (collect ell q t H d)
        (work (D+(limit+1)*(ell+1)+1) ell q t H d)
        (fun s => Reachable ell start (n+1) s.val)
        (RRTraversalWriterM10.budget ell
          (RRNodeTariffM10.tariff (D+(limit+1)*(ell+1)+1) ell q t)
          (terminalBudget (D+(limit+1)*(ell+1)+1)) d)
        (RRTraversalWriterM10.count ell d)
        (fun u cursor hu => ih u hu (by omega) cursor)
        (fun u cursor => candidates ell q t d u H cursor hq) cs hp
        (children ell q t H s c).1.2
      have hm := Nat.mul_le_mul_right
        (RRTraversalWriterM10.budget ell
          (RRNodeTariffM10.tariff (D+(limit+1)*(ell+1)+1) ell q t)
          (terminalBudget (D+(limit+1)*(ell+1)+1)) d+2*RRTraversalWriterM10.count ell d+4) hcs
      omega

#print axioms walk_bound
#print axioms candidates
#print axioms terminal_bound
#print axioms children_reachable
#print axioms work_bound
end AspisR1.RRActualTraversalWorkM10
end
