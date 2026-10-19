-- Exact generated declaration cuts; bodies unchanged.
import AspisR1CuIterator.Types
import AspisR1CuIterator.SourceOption
open Aeneas Aeneas.Std Result ControlFlow Error
namespace AspisR1CuIterator
/-- [aspis_cu_iterator::{impl core::iter::traits::iterator::Iterator<(usize, &'a mut T)> for aspis_cu_iterator::Enumerate<core::slice::iter::IterMut<'a, T>>}::next]:
    Source: 'lib.rs', lines 7:0-12:5
    Visibility: public -/
def EnumerateIterMut.Insts.CoreIterTraitsIteratorIteratorPairUsizeMutAT.next
  {T : Type} (self : Enumerate (core.slice.iter.IterMut T)) :
  Result ((Option (Std.Usize × T)) × (Enumerate (core.slice.iter.IterMut T))
    × (Enumerate (core.slice.iter.IterMut T) → Option (Std.Usize × T) →
    Enumerate (core.slice.iter.IterMut T)))
  := do
  let (o, im, next_back) ← core.slice.iter.IteratorIterMut.next self.iter
  let (cf, branch_back) ←
    core.option.Option.Insts.CoreOpsTry_traitTry.branch o
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let i ← self.count + 1#usize
    let back'a :=
      fun self1 o1 =>
        let t := match o1 with
                 | some (_, t1) => t1
                 | _ => val
        let o2 := branch_back (core.ops.control_flow.ControlFlow.Continue t)
        let im1 := next_back self1.iter o2
        { self with iter := im1 }
    ok (some (self.count, val), { iter := im, count := i }, back'a)
  | core.ops.control_flow.ControlFlow.Break residual =>
    let (o1, _) ←
      core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual
        (Std.Usize × T) residual
    let back'a :=
      fun self1 o2 =>
        let o3 := branch_back cf
        let im1 := next_back self1.iter o3
        { self with iter := im1 }
    ok (o1, { self with iter := im }, back'a)

end AspisR1CuIterator
