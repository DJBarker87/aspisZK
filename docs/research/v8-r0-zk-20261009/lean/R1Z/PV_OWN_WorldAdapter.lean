import R1Z.PV_OWN_Operations
set_option autoImplicit false
namespace R1Z.PV_OWN_WorldAdapter
open PV_W_Enriched PV_W_Threading PV_OWN_Heap
/-- Installing the authoritative heap preserves every other process field.
This is a carrier adapter, not an assertion that a native allocator frames OS,
atomics, statics or captured destructor state. -/
def commit {Os Fs S X : Type} (w : World Os Fs S X) (heap : Heap) : World Os Fs S X :=
 {w with process := {w.process with heap := heap}}

theorem heap {Os Fs S X : Type} (w : World Os Fs S X) (h : Heap) :
 (commit w h).process.heap=h := rfl

theorem carrier {Os Fs S X : Type} (w : World Os Fs S X) (h : Heap) :
 (commit w h).os=w.os ∧ (commit w h).filesystem=w.filesystem ∧
 (commit w h).process.statics=w.process.statics ∧
 (commit w h).process.atomics=w.process.atomics ∧
 (commit w h).process.threadLocal=w.process.threadLocal ∧
 (commit w h).process.unwinding=w.process.unwinding ∧
 (commit w h).process.extra=w.process.extra := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem overwrite {Os Fs S X : Type} (w : World Os Fs S X) (a b : Heap) :
 commit (commit w a) b=commit w b := rfl
#print axioms heap
#print axioms carrier
#print axioms overwrite
end R1Z.PV_OWN_WorldAdapter
