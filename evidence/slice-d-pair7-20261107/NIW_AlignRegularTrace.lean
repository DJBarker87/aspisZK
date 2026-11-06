import NIW_AlignRegularStream
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIW_AlignRegularTrace
open Aeneas Aeneas.Std Result LPi_FieldValues NIT_Cuts NIT_PairControl NIW_AlignRegularStream
variable [FIo_Native.Allocation]

/-- Native-stream to the SAME complete regular call; not a model-to-log
existence theorem. Clause production remains an explicit internal obligation. -/
theorem call (c : Context) (before : Scratch) (events : List Event)
 (observed : Result NHM_RegularKinds.Reply)
 (s2 : c.w.value.variant=FIo_Native.transport.Variant.S2)
 (order : Ordered (NHM_RegularKinds.kinds (NGM_GuardExact.guard c.w.value 2#usize))
  before initial events observed)
 (clauses : ∀ e∈events,Clause c.w.value c.f.value c.ap0.value c.ap1.value e) :
 FIo_Native.weights.process_regular_kinds c.w.value (NGM_GuardExact.guard c.w.value 2#usize)
  c.alpha.value.to_slice c.f.value 2#usize 64#usize c.ap0.value c.ap1.value before initial=observed :=
 (NIW_AlignRegular.source c.w.value _ c.alpha.value.to_slice c.f.value c.ap0.value c.ap1.value
  before initial s2).trans (fold _ _ _ _ _ _ _ _ _ order clauses)

theorem failed (c : Context) (before : Scratch) (events : List Event) (err : Error)
 (s2 : c.w.value.variant=FIo_Native.transport.Variant.S2)
 (order : Ordered (NHM_RegularKinds.kinds (NGM_GuardExact.guard c.w.value 2#usize))
  before initial events (fail err))
 (clauses : ∀ e∈events,Clause c.w.value c.f.value c.ap0.value c.ap1.value e) :
 NIT_RegularChain.Trace c before (fail err) :=
 .failed err (call c before events (fail err) s2 order clauses)

theorem diverged (c : Context) (before : Scratch) (events : List Event)
 (s2 : c.w.value.variant=FIo_Native.transport.Variant.S2)
 (order : Ordered (NHM_RegularKinds.kinds (NGM_GuardExact.guard c.w.value 2#usize))
  before initial events div)
 (clauses : ∀ e∈events,Clause c.w.value c.f.value c.ap0.value c.ap1.value e) :
 NIT_RegularChain.Trace c before div :=
 .diverged (call c before events div s2 order clauses)

theorem returned (c : Context) (before after : Scratch) (parts : Parts) (reply : RU)
 (events : List Event) (out : Result NR)
 (s2 : c.w.value.variant=FIo_Native.transport.Variant.S2)
 (order : Ordered (NHM_RegularKinds.kinds (NGM_GuardExact.guard c.w.value 2#usize))
  before initial events (ok (reply,after,parts)))
 (clauses : ∀ e∈events,Clause c.w.value c.f.value c.ap0.value c.ap1.value e)
 (tail : NIT_RegularChain.After c (NGM_GuardExact.guard c.w.value 2#usize) parts reply out) :
 NIT_RegularChain.Trace c before out :=
 .returned reply after parts out (call c before events _ s2 order clauses) tail

#print axioms call
#print axioms failed
#print axioms diverged
#print axioms returned
end AspisR1.NIW_AlignRegularTrace
