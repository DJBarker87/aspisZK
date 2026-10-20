import Aeneas
import AspisR1SelectedMaskProbe.FunsExternal
open Aeneas Aeneas.Std Result ControlFlow Error

namespace TerminalV4ArrayIntoIterListModel

abbrev IntoIter (T : Type) (_N : Usize) := List T

def intoIter {T : Type} {N : Usize} (a : Array T N) : IntoIter T N := a.1

def next {T : Type} {N : Usize} (xs : IntoIter T N) :
    Result ((Option T) × IntoIter T N) :=
  match xs with
  | [] => .ok (none, [])
  | x :: rest => .ok (some x, rest)

def nextBack {T : Type} {N : Usize} (xs : IntoIter T N) :
    Result ((Option T) × IntoIter T N) :=
  match xs.reverse with
  | [] => .ok (none, [])
  | x :: rest => .ok (some x, rest.reverse)

def iterator (T : Type) {N : Usize} :
    core.iter.traits.iterator.Iterator (IntoIter T N) T :=
  { next := next }

def doubleEndedIterator (T : Type) {N : Usize} :
    core.iter.traits.double_ended.DoubleEndedIterator (IntoIter T N) T :=
  { iteratorInst := iterator T, next_back := nextBack }

def fold {T Acc F : Type} {N : Usize}
    (fn : core.ops.function.FnMut F (Acc × T) Acc) :
    IntoIter T N → Acc → F → Result Acc :=
  core.iter.traits.iterator.Iterator.fold.default (iterator T) fn

theorem intoIter_length {T : Type} {N : Usize} (a : Array T N) :
    (intoIter a).length = N.val := a.2

end TerminalV4ArrayIntoIterListModel

#print axioms TerminalV4ArrayIntoIterListModel.next
#print axioms TerminalV4ArrayIntoIterListModel.nextBack
#print axioms TerminalV4ArrayIntoIterListModel.fold
