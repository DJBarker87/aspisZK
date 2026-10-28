from pathlib import Path
E=Path(__file__).resolve().parent/'NDB_generated'
s='''import NCV_ArrayFrame
set_option autoImplicit false
namespace NDB_PrimaryWords
open Aeneas Aeneas.Std Result

def window (b : Slice U8) (s : Nat) (n : Usize) : Array U8 n :=
  ⟨List.ofFn (fun i : Fin n.val => NCV_ZeroStep.byte b (s+i.val)),by simp⟩

theorem add_read (b : Slice U8) (s k : Usize) (fit : s.val+k.val<b.val.length) :
    ∃ addr : Usize, s+k=ok addr ∧
      Slice.index_usize b addr=ok (NCV_ZeroStep.byte b (s.val+k.val)) := by
  have spec : (s+k : Result Usize) ⦃ x=>x.val=s.val+k.val ⦄ := by
    apply UScalar.add_spec <;> scalar_tac
  obtain ⟨addr,call,value⟩:=WP.spec_imp_exists spec
  refine ⟨addr,call,?_⟩
  simpa only [value] using NCV_ZeroStep.read b addr (by omega)
'''
for bits,n in [(32,4),(64,8)]:
 s+=f'''\ntheorem word{bits} (b : Slice U8) (s : Usize) (fit : s.val+{n} ≤ b.val.length) :
    NCV_Reference.word{bits} b s=ok (core.num.U{bits}.from_le_bytes (window b s.val {n}#usize)) := by
  have rd0:=NCV_ZeroStep.read b s (by omega)
'''
 for k in range(1,n):s+=f'  obtain ⟨addr{k},add{k},rd{k}⟩:=add_read b s {k}#usize (by scalar_tac)\n'
 names=','.join(['rd0']+[f'add{k},rd{k}' for k in range(1,n)])
 s+=f'  simp only [NCV_Reference.word{bits},{names},bind_tc_ok]\n  rfl\n'
s+='\n#print axioms add_read\n#print axioms word32\n#print axioms word64\nend NDB_PrimaryWords\n'
(E/'NDB_PrimaryWords.lean').write_text(s)
