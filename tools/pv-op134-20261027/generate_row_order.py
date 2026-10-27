from pathlib import Path
import re,sys
root=Path(__file__).resolve().parents[2];lean=root/'docs/research/v8-r0-zk-20261009/lean/R1Z'
s='''import R1Z.PV_Op134_RowSpec
import Mathlib.Data.List.Dedup
namespace R1Z.PV_Op134_RowOrder
open Aeneas Aeneas.Std
set_option autoImplicit false

def good (xs : List U16) (lo hi : Nat) : Prop :=
  xs.Pairwise (fun a b => a.val < b.val) ∧ ∀ r ∈ xs, lo ≤ r.val ∧ r.val < hi

theorem append {xs ys : List U16} {lo mid hi : Nat}
    (hx : good xs lo mid) (hy : good ys mid hi) (hlo : lo ≤ mid) (hhi : mid ≤ hi) :
    good (xs ++ ys) lo hi := by
  constructor
  · exact List.pairwise_append.mpr ⟨hx.1,hy.1,by
      intro a ha b hb; have := hx.2 a ha; have := hy.2 b hb; omega⟩
  · intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · have := hx.2 r hr; omega
    · have := hy.2 r hr; omega
'''
s+='attribute [local irreducible] '+' '.join(f'PV_Op134_Rows{i:02}.rows' for i in range(14))+'\n'
bs=[]
for i in range(14):
 vals=list(map(int,re.findall(r'(\d+)#u16',(lean/f'PV_Op134_Rows{i:02}.lean').read_text())))
 bs.append((vals[0],vals[-1]))
s+='theorem ordered_bounds : good PV_Op134_RowSpec.rows 11 1024 := by\n'
for i in range(14):
 lo,hi=bs[i];nxt=bs[i+1][0] if i<13 else 1024
 s+=f'  have b{i} : good PV_Op134_Rows{i:02}.rows {lo} {nxt} := by\n    refine ⟨PV_Op134_Rows{i:02}.sorted,?_⟩\n    intro r hr\n    have := PV_Op134_Rows{i:02}.bounds r hr\n    omega\n'
for i in range(12,-1,-1):
 rhs=f'b{i+1}' if i==12 else f'h{i+1}'
 s+=f'  have h{i} := append b{i} {rhs} (by decide) (by decide)\n'
s+='''  exact h0

theorem sorted : PV_Op134_RowSpec.rows.Pairwise (fun a b => a.val < b.val) := ordered_bounds.1

theorem nodup : PV_Op134_RowSpec.rows.Nodup := by
  exact sorted.imp (by intro a b h heq; subst b; exact (Nat.lt_irrefl _) h)

theorem dedup : PV_Op134_RowSpec.rows.dedup = PV_Op134_RowSpec.rows := nodup.dedup

#print axioms append
#print axioms ordered_bounds
#print axioms sorted
#print axioms nodup
#print axioms dedup
end R1Z.PV_Op134_RowOrder
'''
p=lean/'PV_Op134_RowOrder.lean'
if '--check' in sys.argv:assert p.read_text()==s
else:p.write_text(s)
print('CHECK' if '--check' in sys.argv else 'GENERATED','row ordering')
