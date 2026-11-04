import NFF_Cell
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFF_LoggedEight
open Aeneas Aeneas.Std Result
abbrev Oracle := U32 → U32 → U64

def Law (oracle : Oracle) : Prop := ∀ a b,
  a.val<NEG_DotDomain.P → b.val<NEG_DotDomain.P →
  NEG_ProductAbstraction.Product 64 a.val b.val (oracle a b).val

def cell (oracle : Oracle) (coefficient : Array U32 8#usize) (scalar : U32)
    (sums : Array U64 8#usize) (index : Usize) : Result (Array U64 8#usize) := do
  let word ← Array.index_usize coefficient index
  NFF_Cell.continuation sums index (oracle word scalar)

def ReadCanonical (coefficient : Array U32 8#usize) : Prop := ∀ index word,
  Array.index_usize coefficient index=ok word → word.val<NEG_DotDomain.P

theorem cell_replay (oracle : Oracle) (law : Law oracle)
    (coefficient : Array U32 8#usize) (canonical : ReadCanonical coefficient)
    (scalar : U32) (hs : scalar.val<NEG_DotDomain.P)
    (sums : Array U64 8#usize) (index : Usize) :
    cell oracle coefficient scalar sums index=NFE_NEV_DotCell.cell coefficient scalar sums index := by
  cases read : Array.index_usize coefficient index with
  | fail e => simp only [cell,NFE_NEV_DotCell.cell,read,bind_tc_fail]
  | div => simp only [cell,NFE_NEV_DotCell.cell,read,bind_tc_div]
  | ok word =>
    have hw := canonical index word read
    have h := NFF_Cell.replay coefficient scalar word sums index (oracle word scalar)
      read hw hs (law word scalar hw hs)
    simpa only [cell,read,bind_tc_ok] using h.symm

def eight (oracle : Oracle) (coefficient : Array U32 8#usize) (scalar : U32)
    (sums : Array U64 8#usize) : Result (Array U64 8#usize) := do
  let s1 ← cell oracle coefficient scalar sums 0#usize
  let s2 ← cell oracle coefficient scalar s1 1#usize
  let s3 ← cell oracle coefficient scalar s2 2#usize
  let s4 ← cell oracle coefficient scalar s3 3#usize
  let s5 ← cell oracle coefficient scalar s4 4#usize
  let s6 ← cell oracle coefficient scalar s5 5#usize
  let s7 ← cell oracle coefficient scalar s6 6#usize
  let s8 ← cell oracle coefficient scalar s7 7#usize
  ok s8

theorem replay (oracle : Oracle) (law : Law oracle)
    (coefficient : Array U32 8#usize) (canonical : ReadCanonical coefficient)
    (scalar : U32) (hs : scalar.val<NEG_DotDomain.P) (sums : Array U64 8#usize) :
    eight oracle coefficient scalar sums=NFE_NEV_DotEight.eight coefficient scalar sums := by
  simp only [eight,NFE_NEV_DotEight.eight,cell_replay oracle law coefficient canonical scalar hs]

#print axioms cell_replay
#print axioms replay
end AspisR1.NFF_LoggedEight
end
