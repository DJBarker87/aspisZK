#!/usr/bin/env python3
"""Emit bounded field observations and scalar occupancy cases, never decoder reduction."""
import argparse
import hashlib
import json
from pathlib import Path


def render():
    text = '''import JHu_FrontierRun
import JHu_FixtureDigests
import Mathlib.Tactic.IntervalCases
set_option autoImplicit false
namespace AspisR1.JHu_FrontierFixture
open Aeneas Aeneas.Std Result
local instance : Inhabited (Array U32 (Usize.ofNatCore 8 (8#usize).hBounds)) :=
  ⟨Array.repeat 8#usize 0#u32⟩

/-- Each read uses its independently checked digest field, with symbolic address transport. -/
theorem reads : ∀ (n : Nat), n<20 → ∀ addr : Usize, addr.val=48+32*n →
    NCV_Reference.digest JHu_FixtureDigests.tree addr=
      ok (.Ok (NCV_ArrayFrame.coord JFt_SnapshotValue.value.frontier n)) := by
  intro n hn
  interval_cases n
'''
    for index in range(20):
        address = 48 + 32 * index
        text += f'''  · intro addr ha
    have same : addr={address}#usize := UScalar.eq_of_val_eq ha
    subst addr
    change NCV_Reference.digest JHu_FixtureDigests.tree {address}#usize=ok (.Ok JFt_Digest{index+2:02}.value)
    exact JHu_FixtureDigests.frontier_{index:02}
'''
    text += '''#print axioms reads

/-- Twenty scalar occupancy cases, selecting only the corresponding eight-limb empty row. -/
theorem bits : ∀ (n : Nat), n<20 → ∀ i : Usize, i.val=n → ∃ tag : U64,
    13#u64 >>> i=ok tag ∧ (tag &&& 1#u64=0#u64 →
      NCV_ArrayFrame.coord JFt_SnapshotValue.value.frontier n=NCV_ArrayFrame.coord NCV_Reference.EMPTY n) := by
  intro n hn
  interval_cases n
'''
    for index in range(20):
        tag = 13 >> index
        text += f'''  · intro i hi
    have same : i={index}#usize := UScalar.eq_of_val_eq hi
    subst i
    refine ⟨{tag}#u64,by rfl,?_⟩
'''
        if tag & 1:
            text += f'''    intro h
    have no : ¬({tag}#u64 &&& 1#u64=0#u64) := by decide
    exact False.elim (no h)
'''
        else:
            text += f'''    intro _
    change JFt_Digest{index+2:02}.value=NCV_ArrayFrame.coord NCV_Reference.EMPTY {index}
    simp only [NCV_Reference.EMPTY,NCV_ArrayFrame.coord,List.getElem?_cons_succ,
      List.getElem?_cons_zero,Option.getD_some,JFt_Digest{index+2:02}.value,Array.make]
'''
    return text + '''#print axioms bits

theorem source : NCV_Reference.decode_frontier JHu_FixtureDigests.tree 13#u64=
    ok (.Ok JFt_SnapshotValue.value.frontier) := by
  apply JHu_FrontierRun.source
  · intro i addr hi ha
    exact reads i.val hi addr ha
  · intro i hi
    exact bits i.val hi i rfl
#print axioms source
end AspisR1.JHu_FrontierFixture
'''


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    target = Path(__file__).resolve().parents[2] / 'lean/JHu_FrontierFixture.lean'
    result = render().encode()
    if args.check:
        assert target.read_bytes() == result, 'Generated frontier observations differ'
    else:
        target.write_bytes(result)
    print(json.dumps(dict(check=args.check, target=str(target),
                          sha256=hashlib.sha256(result).hexdigest(),
                          field_reads=20, occupied_rows=[0, 2, 3],
                          empty_rows=[1] + list(range(4, 20)),
                          theorem_consumer='AspisR1.JHu_Lane.source')))
