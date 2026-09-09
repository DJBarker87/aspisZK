import AspisFormal.Pool.V7PairForestCuArithmeticEquivalences
import AspisFormal.V5ComponentCQM31TowerExact

/-! Source-shaped positive-transfer terminal insertion. This proves the
current packer's field-coordinate formula, reverse-Horner ordering and full
masked-terminal delta. Integer reduction/canonical parsing, generated source
translation and probabilistic acceptance enforcement remain separate.
-/
set_option autoImplicit false
namespace AspisV8.PositiveTerminalInsertion
open AspisPool.V7PairForestCuArithmeticEquivalences
open AspisV5ComponentCQM31TowerExact

def towerI : QM31Exact := ⟨⟨0,1⟩,0⟩
def towerU : QM31Exact := ⟨0,1⟩

-- Typed projections keep the simplifier from having to rediscover the two
-- nested tower parameters after reducing a concrete basis constructor.
theorem qm_re_mul (x y : QM31Exact) :
    (x*y).re=x.re*y.re+qm31R*x.im*y.im := rfl
theorem qm_im_mul (x y : QM31Exact) :
    (x*y).im=x.re*y.im+x.im*y.re+0*x.im*y.im := rfl
theorem cm_re_mul (x y : CM31Exact) :
    (x*y).re=x.re*y.re+(-1)*x.im*y.im := rfl
theorem cm_im_mul (x y : CM31Exact) :
    (x*y).im=x.re*y.im+x.im*y.re+0*x.im*y.im := rfl

/-- Field reduction of the four literal signed limb accumulators in the
current Rust qm31_pack_base4; inputs are arbitrary QM31, not just M31. -/
def literalPack (v : Fin 4 → QM31Exact) : QM31Exact :=
  ⟨⟨(v 0).re.re-(v 1).re.im+2*(v 2).im.re-(v 2).im.im-
        (v 3).im.re-2*(v 3).im.im,
      (v 0).re.im+(v 1).re.re+(v 2).im.re+2*(v 2).im.im+
        2*(v 3).im.re-(v 3).im.im⟩,
    ⟨(v 0).im.re-(v 1).im.im+(v 2).re.re-(v 3).re.im,
      (v 0).im.im+(v 1).im.re+(v 2).re.im+(v 3).re.re⟩⟩

theorem literalPack_eq_tower_map (v : Fin 4 → QM31Exact) :
    literalPack v=packBase4 towerI towerU v := by
  ext <;> simp [literalPack,packBase4,towerI,towerU,qm31R,
    qm_re_mul,qm_im_mul,cm_re_mul,cm_im_mul] <;> ring

/-- Unlike a base-input-only coordinate assembly, this handles a full
extension-valued off-domain selector times a cubic residual. -/
theorem literalPack_slot2 (w : QM31Exact) :
    literalPack ![0,0,w,0]=towerU*w := by
  rw [literalPack_eq_tower_map]
  simp [packBase4]

def addSlot2 {K : Type*} [Add K] (v : Fin 4 → K) (w : K) : Fin 4 → K :=
  ![v 0,v 1,v 2+w,v 3]

theorem pack_slot2_add {K : Type*} [CommRing K]
    (i u : K) (v : Fin 4 → K) (w : K) :
    packBase4 i u (addSlot2 v w)=
      packBase4 i u v+packBase4 i u ![0,0,w,0] := by
  simp [addSlot2,packBase4]
  ring

/-- Consumes V7's existing shared-selector identity at the literal tower. -/
theorem literalPack_shared_selector (s : QM31Exact) (v : Fin 4 → QM31Exact) :
    literalPack (fun j=>s*v j)=s*literalPack v := by
  rw [literalPack_eq_tower_map,literalPack_eq_tower_map]
  exact packBase4_shared_selector towerI towerU s v

def horner {K : Type*} [Mul K] [Add K] (theta : K) (lanes : List K) (a : K) : K :=
  lanes.foldr (fun lane acc=>theta*acc+lane) a

/-- Identifies the actual reverse Rust loop, without expanding its lanes. -/
theorem horner_eq_reverse_loop {K : Type*} [Mul K] [Add K]
    (theta : K) (lanes : List K) (a : K) :
    lanes.reverse.foldl (fun acc lane=>theta*acc+lane) a=horner theta lanes a :=
  List.foldl_reverse

theorem horner_append {K : Type*} [Mul K] [Add K]
    (theta : K) (xs ys : List K) (a : K) :
    horner theta (xs++ys) a=horner theta xs (horner theta ys a) :=
  List.foldr_append

theorem horner_singleton {K : Type*} [Mul K] [Add K] (theta lane a : K) :
    horner theta [lane] a=theta*a+lane := rfl

theorem horner_initial_add {K : Type*} [CommRing K]
    (theta : K) (lanes : List K) (a delta : K) :
    horner theta lanes (a+delta)=horner theta lanes a+theta^lanes.length*delta := by
  induction lanes with
  | nil => simp [horner]
  | cons lane tail ih =>
    change theta*horner theta tail (a+delta)+lane=
      (theta*horner theta tail a+lane)+theta^(tail.length+1)*delta
    rw [ih,pow_succ]
    ring

/-- The last semantic pack is processed first, after the Copy accumulator;
its change then crosses every earlier semantic and every Poseidon pack. -/
theorem two_loop_last_insertion {K : Type*} [CommRing K]
    (theta copy last delta : K) (poseidon lowerSemantic : List K) :
    horner theta poseidon (horner theta (lowerSemantic++[last+delta]) copy)=
      horner theta poseidon (horner theta (lowerSemantic++[last]) copy)+
        theta^(lowerSemantic.length+poseidon.length)*delta := by
  rw [horner_append,horner_append]
  simp only [horner_singleton]
  rw [←add_assoc (theta*copy) last delta,horner_initial_add,horner_initial_add]
  congr 1
  rw [←mul_assoc,←pow_add,Nat.add_comm lowerSemantic.length poseidon.length]

def sourceComposition {K : Type*} [CommRing K]
    (i u theta copy : K) (poseidon lowerSemantic : List K) (last : Fin 4 → K) : K :=
  horner theta poseidon (horner theta (lowerSemantic++[packBase4 i u last]) copy)

theorem source_lane94_insertion {K : Type*} [CommRing K]
    (i u theta copy : K) (poseidon lowerSemantic : List K)
    (hp : poseidon.length=4) (hs : lowerSemantic.length=23)
    (last : Fin 4 → K) (weightedResidual : K) :
    sourceComposition i u theta copy poseidon lowerSemantic (addSlot2 last weightedResidual)=
      sourceComposition i u theta copy poseidon lowerSemantic last+
        theta^27*packBase4 i u ![0,0,weightedResidual,0] := by
  unfold sourceComposition
  rw [pack_slot2_add,two_loop_last_insertion,hp,hs]

theorem lane94_indices :
    94/4=23 ∧ 94%4=2 ∧ 23+4=27 ∧ 4+24+1=29 := by decide

/-- Matches composition_delta's square preparation without field inversion. -/
def prepared27 {K : Type*} [Mul K] (theta : K) : K :=
  let t2:=theta*theta
  let t4:=t2*t2
  let t8:=t4*t4
  let t16:=t8*t8
  t16*t8*t2*theta

theorem prepared27_eq {K : Type*} [CommRing K] (theta : K) :
    prepared27 theta=theta^27 := by
  unfold prepared27
  ring

/-- The old mask value, H and inactive-H claims are arbitrary and unchanged;
the correction does not replace the degree-two mu aggregate. -/
def maskedTerminal {K : Type*} [CommRing K]
    (mask eta eqWeight mu h inactiveH composition : K) : K :=
  mask+eta*(eqWeight*composition+mu*h+mu*mu*inactiveH)

theorem maskedTerminal_delta {K : Type*} [CommRing K]
    (mask eta eqWeight mu h inactiveH composition delta : K) :
    maskedTerminal mask eta eqWeight mu h inactiveH (composition+delta)=
      maskedTerminal mask eta eqWeight mu h inactiveH composition+eta*(eqWeight*delta) := by
  unfold maskedTerminal
  ring

/-- Concrete-field endpoint for the isolated Rust wrapper. All values,
including zero challenges and arbitrary prior residuals, are permitted.
The local slot is added to (not assumed to replace a sound) ordinary batch. -/
theorem positive_terminal_insertion
    (theta copy mask eta eqWeight mu h inactiveH selector r c inv : QM31Exact)
    (poseidon lowerSemantic : List QM31Exact)
    (hp : poseidon.length=4) (hs : lowerSemantic.length=23)
    (last : Fin 4 → QM31Exact) :
    maskedTerminal mask eta eqWeight mu h inactiveH
      (sourceComposition towerI towerU theta copy poseidon lowerSemantic
        (addSlot2 last (selector*(r*c*inv-1)))) =
    maskedTerminal mask eta eqWeight mu h inactiveH
      (sourceComposition towerI towerU theta copy poseidon lowerSemantic last)+
      eta*(eqWeight*(prepared27 theta*literalPack ![0,0,selector*(r*c*inv-1),0])) := by
  rw [source_lane94_insertion _ _ _ _ _ _ hp hs,maskedTerminal_delta,
    prepared27_eq,literalPack_eq_tower_map]

#print axioms literalPack_eq_tower_map
#print axioms literalPack_slot2
#print axioms literalPack_shared_selector
#print axioms horner_eq_reverse_loop
#print axioms horner_initial_add
#print axioms two_loop_last_insertion
#print axioms source_lane94_insertion
#print axioms lane94_indices
#print axioms prepared27_eq
#print axioms maskedTerminal_delta
#print axioms positive_terminal_insertion
end AspisV8.PositiveTerminalInsertion
