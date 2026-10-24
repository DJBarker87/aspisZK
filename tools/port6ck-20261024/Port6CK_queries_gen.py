from pathlib import Path
P=Path('docs/research/100bit-spend-path-20261013/lean')
s='''import Port6CK_Roots
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port6CK_Queries
open Aeneas Aeneas.Std Result AspisR1Stage2
open Port6CK_Roots (Raw)
def read (raw : Raw) (r : verifier.Reader) : Result (Array U32 22#usize × verifier.Reader) := do
'''
for i in range(22):
 r='r' if i==0 else f'r{i}'
 s+=f'  let (b{i},r{i+1}) ← raw 4#usize {r}\n  let q{i} ← lift (core.num.U32.from_le_bytes b{i})\n'
s+='  ok (Array.make 22#usize ['+','.join(f'q{i}' for i in range(22))+'],r22)\n'
# CPS form mirrors the parent literally; bind normalization stays local here.
body=s[s.index('  let (b0'):s.index('\ntheorem reference') if '\ntheorem reference' in s else len(s)]
body=body.replace('  ok (Array.make 22#usize [','  next (Array.make 22#usize [').replace('],r22)',']) r22')
s+='\ndef cps {T : Type} (raw : Raw) (r : verifier.Reader)\n    (next : Array U32 22#usize → verifier.Reader → Result T) : Result T := do\n'+body
s+='''

theorem cps_bind {T : Type} (raw : Raw) (r : verifier.Reader)
    (next : Array U32 22#usize → verifier.Reader → Result T) :
    cps raw r next = (do let (q,out) ← read raw r; next q out) := by
  simp only [cps,read,bind_assoc_eq,bind_tc_ok,Aeneas.Std.uncurry]
  rfl
'''
s+='''
theorem reference
    (unwrap : (N : Usize) → core.result.Result (Array U8 N) core.array.TryFromSliceError → Result (Array U8 N))
    (unwrap_ok : ∀ N b, unwrap N (.Ok b)=ok b)
    (r : verifier.Reader) (room : r.at.val+88≤r.bytes.val.length) (size : r.bytes.val.length≤4096) :
    read (fun N => Port5Q2_ReaderRaw.raw N (unwrap N)) r =
      read CheckpointBytes3Reader.raw r := by
  unfold read
  dsimp only
'''
for i in range(22):
 r='r' if i==0 else f'r{i}'
 s+=f'''  rw [Port5Q2_ReaderRaw.reference 4#usize (unwrap _) (unwrap_ok _) {r} (by change {r}.at.val+4≤{r}.bytes.val.length; omega) (by omega)]
'''
 if i<21:
  s+=f'''  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro pair called
  rcases pair with ⟨b{i},r{i+1}⟩
  simp only [Aeneas.Std.uncurry]
  obtain ⟨contents,cursor,backing⟩ := CheckpointBytes4RawFields.raw_success 4#usize {r} r{i+1} b{i} (by change {r}.at.val+4≤{r}.bytes.val.length; omega) called
  change r{i+1}.at.val={r}.at.val+4 at cursor
  have room : r{i+1}.at.val+{4*(21-i)}≤r{i+1}.bytes.val.length := by rw [cursor,backing]; omega
  have size : r{i+1}.bytes.val.length≤4096 := by rw [backing]; omega
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro query decoded
'''
s+='''
#print axioms cps_bind\n#print axioms reference
end AspisR1.Port6CK_Queries
end
'''
(P/'Port6CK_Queries.lean').write_text(s)
