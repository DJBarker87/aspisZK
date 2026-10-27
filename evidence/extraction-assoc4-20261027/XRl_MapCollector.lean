import XRl_Collector
open Aeneas Aeneas.Std Result
namespace XRl_MapCollector
/-- Same dictionary body used by XRk_StdExtra's mapped collector. -/
def iterator {I F T B : Type} (it : core.iter.traits.iterator.Iterator I T)
    (fn : core.ops.function.FnMut F T B) :
    core.iter.traits.iterator.Iterator (core.iter.adapters.map.Map I F) B :=
  { next := fun s => do
      let (v,i) ← it.next s.iter
      match v with
      | none => ok (none,{s with iter := i})
      | some v => do
        let (b,f) ← fn.call_mut s.f v
        ok (some b,⟨i,f⟩) }

theorem terminal {I F T B : Type} (it : core.iter.traits.iterator.Iterator I T)
    (fn : core.ops.function.FnMut F T B) (remaining : I → Nat)
    (stop : ∀ s next, it.next s = ok (none,next) → remaining s = 0)
    (s next : core.iter.adapters.map.Map I F)
    (run : (iterator it fn).next s=ok (none,next)) : remaining s.iter=0 := by
  unfold iterator at run
  obtain ⟨value,i,hnext,run⟩ := XRk_ResultTools.pair_bind_success _ _ _ run
  cases value with
  | none => exact stop s.iter i hnext
  | some value =>
    obtain ⟨b,f,_,run⟩ := XRk_ResultTools.pair_bind_success _ _ _ run
    cases run

theorem advance {I F T B : Type} (it : core.iter.traits.iterator.Iterator I T)
    (fn : core.ops.function.FnMut F T B) (remaining : I → Nat)
    (step : ∀ s item next, it.next s=ok (some item,next) → remaining s=remaining next+1)
    (s next : core.iter.adapters.map.Map I F) (item : B)
    (run : (iterator it fn).next s=ok (some item,next)) : remaining s.iter=remaining next.iter+1 := by
  unfold iterator at run
  obtain ⟨value,i,hnext,run⟩ := XRk_ResultTools.pair_bind_success _ _ _ run
  cases value with
  | none => cases run
  | some value =>
    obtain ⟨b,f,_,run⟩ := XRk_ResultTools.pair_bind_success _ _ _ run
    have same := congrArg Prod.snd (Result.ok.inj run)
    have hi := congrArg core.iter.adapters.map.Map.iter same
    change i=next.iter at hi
    rw [←hi]
    exact step s.iter value i hnext

theorem length {I F T B : Type} (it : core.iter.traits.iterator.Iterator I T)
    (fn : core.ops.function.FnMut F T B) (remaining : I → Nat)
    (stop : ∀ s next, it.next s=ok (none,next) → remaining s=0)
    (step : ∀ s item next, it.next s=ok (some item,next) → remaining s=remaining next+1)
    (s : core.iter.adapters.map.Map I F) (acc out : List B)
    (run : alloc.vec.FromIteratorVec.iterToList (iterator it fn) s acc=ok out) :
    out.length=acc.length+remaining s.iter :=
  XRl_Collector.length (iterator it fn) (fun s => remaining s.iter)
    (fun s next run => terminal it fn remaining stop s next run)
    (fun s item next run => advance it fn remaining step s next item run) s acc out run
#print axioms terminal
#print axioms advance
#print axioms length
end XRl_MapCollector
