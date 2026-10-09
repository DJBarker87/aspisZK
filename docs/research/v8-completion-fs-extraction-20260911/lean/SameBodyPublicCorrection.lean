import SameBodyAssembly
set_option autoImplicit false
namespace AspisV8Completion.SameBodyPublicCorrection
universe u v
variable {K : Type u} {Schedule : Type v}
open SameBodyOrdinary (Arithmetic Point Prepared)
open SameBodyRelation (Word Strategy)

/-- Only group zero is used by entries0,1,2. Literal source constants are
INACTIVE_ROW_GROUPS[0]=0 and INACTIVE_GROUP_MASKS[0]=59391 at parent7e947e6a.
This is not a caller-provided mask or claimed table fingerprint. -/
def firstMaskBit (i : Fin 3) : Nat := (59391 / 2^i.val) % 2
theorem first_mask_bits (i : Fin 3) : firstMaskBit i = 1 := by
  have h : i.val=0 ∨ i.val=1 ∨ i.val=2 := by omega
  rcases h with h | h | h <;> simp [firstMaskBit,h]

/-- Literal v6_statement_points carry loop: coordinate9 first, then8..0.
No Booleanity of z is assumed. -/
def successor (ops : Arithmetic K) (z : Fin 10 → K) : Fin 10 → K :=
  let initial : (Fin 10 → K) × K := (fun i => if i.val=9 then ops.sub ops.one (z 9) else z i, z 9)
  ((List.finRange 9).reverse.foldl (fun (state : (Fin 10 → K) × K) i =>
    let j : Fin 10 := ⟨i.val, by omega⟩
    let both := ops.mul (z j) state.2
    let next := ops.sub (ops.add (z j) state.2) (ops.add both both)
    ((fun k => if k.val=j.val then next else state.1 k),both)) initial).1

def points (ops : Arithmetic K) (z : Fin 10 → K) : Fin 3 → Fin 10 → K :=
  fun row => if row.val=0 then z else if row.val=1 then successor ops z
    else fun i => if i.val=7 ∨ i.val=6 then ops.sub ops.one (z i) else z i

/-- Literal reference Description::entry for the only three entries needed.
The initial one is justified by the frozen mask bit calculation above. -/
def entry (ops : Arithmetic K) (z : Fin 10 → K) (kappa : K) (index : Fin 3) : K :=
  (List.finRange 3).foldl (fun total r =>
    let value := (List.finRange 10).foldl (fun acc j =>
      ops.mul acc (if (index.val / 2^(9-j.val))%2=0
        then ops.sub ops.one (points ops z r j) else points ops z r j))
      (SameBodyOrdinary.scales ops kappa r)
    ops.add total value) ops.one

/-- Literal selected v8_shared_weights Description::entry_pair. It derives
both needed weights from public z,kappa and fixed mask bits; never receives
a freely supplied ordinary vector or weight digest. -/
def pair (ops : Arithmetic K) (z : Fin 10 → K) (kappa : K) (useX : Bool) : K × K :=
  let target : Fin 10 := if useX then 8 else 9
  (List.finRange 3).foldl (fun total r =>
    let common := (List.finRange 10).foldl (fun acc j =>
      if j=target then acc else ops.mul acc (ops.sub ops.one (points ops z r j)))
      (SameBodyOrdinary.scales ops kappa r)
    let right := ops.mul common (points ops z r target)
    (ops.add total.1 (ops.sub common right),ops.add total.2 right)) (ops.one,ops.one)

structure Corrected (K : Type u) where
  prepared : Prepared K
  publicPair : K × K
  claim : K

/-- Same-word scalar preparation followed by the selected shared affine
correction, including its sequential subtraction order. -/
def correct [DecidableEq K] (ops : Arithmetic K) (w : Word K)
    (gamma kappa : K) (p0 p1 : Point K) (z : Fin 10 → K) : Option (Corrected K) :=
  (SameBodyOrdinary.prepare ops w gamma kappa p0 p1).map fun prepared =>
    let weights := pair ops z kappa prepared.useX
    ⟨prepared,weights,
      ops.sub (ops.sub prepared.uncorrectedClaim (ops.mul prepared.intercept weights.1))
        (ops.mul prepared.slope weights.2)⟩

theorem correction_constructed [DecidableEq K] (ops : Arithmetic K) (w : Word K)
    (gamma kappa : K) (p0 p1 : Point K) (z : Fin 10 → K) (out : Corrected K)
    (success : correct ops w gamma kappa p0 p1 z = some out) :
    SameBodyOrdinary.prepare ops w gamma kappa p0 p1 = some out.prepared ∧
    out.publicPair = pair ops z kappa out.prepared.useX ∧
    out.claim = ops.sub
      (ops.sub out.prepared.uncorrectedClaim (ops.mul out.prepared.intercept out.publicPair.1))
      (ops.mul out.prepared.slope out.publicPair.2) := by
  cases h : SameBodyOrdinary.prepare ops w gamma kappa p0 p1 with
  | none => simp [correct,h] at success
  | some p =>
    simp only [correct,h,Option.map_some,Option.some.injEq] at success
    subst out
    exact ⟨rfl,rfl,rfl⟩

/-- ALL legal later relation continuations preserve this exact constructor
at the same earlier z, points, gamma and kappa, including inverse rejection.
Their source/transcript production is not assumed proved. -/
theorem correction_preserved [DecidableEq K] (ops : Arithmetic K) (w : Word K)
    (strategy : Strategy K Schedule) (gamma kappa tau alpha : K)
    (p0 p1 : Point K) (z : Fin 10 → K) (queries : Schedule) (rho : K) (coins : Fin 3 → K) :
    correct ops (SameBodyRelation.produce (SameBodyAssembly.early w)
      strategy tau alpha queries rho coins) gamma kappa p0 p1 z =
      correct ops w gamma kappa p0 p1 z := by
  simp only [correct, SameBodyAssembly.preserves_ordinary]

/- Executable small-field controls, not field-equivalence certificates. -/
private def mod17 : Arithmetic Nat := ⟨0,1,fun a b => (a+b)%17,
  fun a b => (a+17-b%17)%17,fun a b => a*b%17,fun a => a*a%17,
  fun a => (List.range 17).find? (fun b => a*b%17==1)⟩
private def control (seed : Nat) (useX : Bool) : Bool :=
  let z : Fin 10 → Nat := fun i => (seed*7+i.val*3)%17
  let k := seed%17
  let weights := pair mod17 z k useX
  weights.1 == entry mod17 z k 0 && weights.2 == entry mod17 z k (if useX then 2 else 1)
#guard (List.range 32).all (fun seed => control seed true && control seed false)
private def zeroZ : Fin 10 → Nat := fun _ => 0
#guard pair mod17 zeroZ 0 true == (1,1)
#guard !(correct mod17 (fun _ => 0) 1 1 ⟨1,0⟩ ⟨1,0⟩ zeroZ).isSome
#guard (correct mod17 (fun _ => 0) 1 1 ⟨1,0⟩ ⟨0,1⟩ zeroZ).isSome

#print axioms first_mask_bits
#print axioms correction_constructed
#print axioms correction_preserved
end AspisV8Completion.SameBodyPublicCorrection
