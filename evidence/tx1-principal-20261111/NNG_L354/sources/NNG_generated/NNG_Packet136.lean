import NNG_PacketContext136
import NNG_CallEffects136
import NNG_ConcreteRounds136
import NNG_ConcreteClaims136
import NNG_ConcreteTerminal136
import NNG_ConcreteRecords136
import NNG_ConcreteArithmetic136
import NNG_ConcreteMaskDomain136
import NNG_ConcreteCircle136
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_Packet136
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted NNG_Transport
open NNG_Representation136 NNG_DOccurrenceLaws136

theorem closed (a : Args) (obs : RSL.Observer) (env : RSL.Env) (domain : RSL.TX1_136.Domain VL a) :
    Laws VL a (project a) (calls a env) (input a obs env) (NNG_Producer136.events a) env
      (NNG_FinishTree.tree (calls a env) (input a obs env)) := by
  have valid := NNG_PacketContext136.checked a obs env domain
  refine { inputs := inputs a obs env, fromFn := rfl, mapErr := rfl, pointEq := rfl, qeq := rfl,
    mark := ?_, rounds := ?_, claims := ?_, terminal := ?_, mask := ?_, record25 := ?_, extra := ?_,
    multiply := ?_, addMask := ?_, addExtra := ?_, state := ?_, circle0 := ?_, record26 := ?_,
    beforeZ1 := ?_, circle1 := ?_, payload2 := ?_, roundsCanonical := ?_, addExtraCanonical := ?_ }
  · intro site rawObs i entered
    exact NNG_CallEffects136.mark env site rawObs i
  · intro entered
    dsimp only [NNG_Producer136.events]
    rw [NNG_CallEffects136.nonUnit _ _ _ _ _ (NNG_NonUnit136.wireResult _)]
    exact NNG_ConcreteRounds136.occurrence a.challenges.eta env a.prefix_ a.transcript domain.2.2
  · intro entered
    dsimp only [NNG_Producer136.events]
    rw [NNG_CallEffects136.nonUnit _ _ _ _ _ (NNG_NonUnit136.wireResult _)]
    exact NNG_ConcreteClaims136.occurrence a.challenges.eta env a.prefix_ domain.2.2
  · intro claims alpha entered
    have checked := (valid _ entered).terminal
    have domains := (NNG_TypedDomains136.same "terminal" NNG_TypedDomains136.terminal _ _).mp checked
    dsimp only [NNG_Producer136.events]
    rw [NNG_CallEffects136.nonUnit _ _ _ _ _ NNG_NonUnit136.terminalResult]
    have old := NNG_ConcreteTerminal136.occurrence a.challenges.eta env
      (a.public_,NNG_LIBArrays.projectClaims a.challenges.eta claims,NNG_LIBArrays.projectArray a.challenges.eta alpha,a.challenges)
      (NNG_PacketContext136.public_domain a domain)
    rw [NNG_LIBClaimsDomain.lower_project a.challenges.eta claims domains.1,
      NNG_LIBArrayDomain.lower_project_array a.challenges.eta alpha domains.2] at old
    simpa only [NNG_PacketContext136.orig_identity] using old
  · intro claims alpha entered
    have checked := (valid _ entered).mask
    have domains := (NNG_TypedDomains136.same "mask" NNG_TypedDomains136.mask _ _).mp checked
    dsimp only [NNG_Producer136.events]
    rw [NNG_CallEffects136.nonUnit _ _ _ _ _ NNG_NonUnit136.scalar]
    exact NNG_ConcreteMaskDomain136.occurrence a.challenges.eta env claims alpha
      domains.1 domains.2.1 domains.2.2.1 domains.2.2.2
  · intro entered
    dsimp only [NNG_Producer136.events]
    rw [NNG_CallEffects136.nonUnit _ _ _ _ _ (NNG_NonUnit136.wireResult _)]
    exact NNG_ConcreteRecords136.record25 env a.prefix_
  · intro rec entered
    have checked := (valid _ entered).extra
    have own := (NNG_TypedDomains136.same "extra" NNG_TypedDomains136.decode _ _).mp checked
    dsimp only [NNG_Producer136.events]
    rw [NNG_CallEffects136.nonUnit _ _ _ _ _ (NNG_NonUnit136.wireResult _)]
    exact NNG_ConcreteRecords136.extra a.challenges.eta env rec own
  · intro x y entered
    have checked := (valid _ entered).multiply
    have domains := (NNG_TypedDomains136.same "multiply" NNG_TypedDomains136.arithmetic _ _).mp checked
    dsimp only [NNG_Producer136.events]
    rw [NNG_CallEffects136.nonUnit _ _ _ _ _ NNG_NonUnit136.scalar]
    exact NNG_ConcreteArithmetic136.multiply a.challenges.eta env x y domains.1 domains.2
  · intro x y entered
    have checked := (valid _ entered).addMask
    have domains := (NNG_TypedDomains136.same "addMask" NNG_TypedDomains136.arithmetic _ _).mp checked
    dsimp only [NNG_Producer136.events]
    rw [NNG_CallEffects136.nonUnit _ _ _ _ _ NNG_NonUnit136.scalar]
    exact NNG_ConcreteArithmetic136.addMask a.challenges.eta env x y domains.1 domains.2
  · intro x y entered
    have checked := (valid _ entered).addExtra
    have domains := (NNG_TypedDomains136.same "addExtra" NNG_TypedDomains136.arithmetic _ _).mp checked
    dsimp only [NNG_Producer136.events]
    rw [NNG_CallEffects136.nonUnit _ _ _ _ _ NNG_NonUnit136.scalar]
    exact NNG_ConcreteArithmetic136.addExtra a.challenges.eta env x y domains.1 domains.2
  · intro t entered
    dsimp only [NNG_Producer136.events]
    rw [NNG_CallEffects136.nonUnit _ _ _ _ _ NNG_NonUnit136.state]
    exact NNG_ConcreteRecords136.state env t
  · intro t rec entered
    have checked := (valid _ entered).circle0
    have frame := (NNG_TypedDomains136.same "circle0" NNG_TypedDomains136.circle _ _).mp checked
    dsimp only [NNG_Producer136.events]
    rw [NNG_CallEffects136.nonUnit _ _ _ _ _ (NNG_NonUnit136.circleReply t)]
    exact NNG_ConcreteCircle136.circle0 env t rec frame
  · intro entered
    dsimp only [NNG_Producer136.events]
    rw [NNG_CallEffects136.nonUnit _ _ _ _ _ (NNG_NonUnit136.wireResult _)]
    exact NNG_ConcreteRecords136.record26 env a.prefix_
  · intro rec entered
    have checked := (valid _ entered).beforeZ1
    have own := (NNG_TypedDomains136.same "beforeZ1" NNG_TypedDomains136.decode _ _).mp checked
    dsimp only [NNG_Producer136.events]
    rw [NNG_CallEffects136.nonUnit _ _ _ _ _ (NNG_NonUnit136.wireResult _)]
    exact NNG_ConcreteRecords136.beforeZ1 a.challenges.eta env rec own
  · intro t rec entered
    have checked := (valid _ entered).circle1
    have frame := (NNG_TypedDomains136.same "circle1" NNG_TypedDomains136.circle _ _).mp checked
    dsimp only [NNG_Producer136.events]
    rw [NNG_CallEffects136.nonUnit _ _ _ _ _ (NNG_NonUnit136.circleReply t)]
    exact NNG_ConcreteCircle136.circle1 env t rec frame
  · intro entered
    dsimp only [NNG_Producer136.events]
    rw [NNG_CallEffects136.nonUnit _ _ _ _ _ (NNG_NonUnit136.wireResult _)]
    exact NNG_ConcreteRecords136.payload2 env a.prefix_
  · intro entered running alpha t1 returned
    exact (NNG_LIBRoundsCanonical.returned a.prefix_ (input a obs env).digest (input a obs env).transcript
      running alpha t1 returned).1
  · intro x y entered q returned
    have checked := (valid _ entered).addExtra
    have domains := (NNG_TypedDomains136.same "addExtra" NNG_TypedDomains136.arithmetic _ _).mp checked
    exact NNG_LIBField.add_returned a.challenges.eta x y q domains.1 domains.2 returned
#print axioms closed
end AspisR1.NNG_Packet136
