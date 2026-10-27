import Aeneas
open Aeneas Aeneas.Std Result
/- Diagnostic only; expected to fail. Isolates the exact expression at raw
   XRh_Release.Funs:56 against the pinned library, independently of all externals.
   No theorem/object from this failed module is accepted or imported. -/
def XRj_IteratorAbiProbe (T : Type) :
    core.iter.traits.iterator.Iterator (core.slice.iter.IterMut T) T := {
  next := core.slice.iter.IteratorIterMut.next
}
