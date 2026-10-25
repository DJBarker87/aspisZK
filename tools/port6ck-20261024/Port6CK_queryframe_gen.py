from pathlib import Path
P=Path('docs/research/100bit-spend-path-20261013/lean')
s='''import Port6CK_Queries
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port6CK_QueryFrame
open Aeneas Aeneas.Std Result AspisR1Stage2

theorem reached (r out : verifier.Reader) (q : Array U32 22#usize)
    (room : r.at.val+88≤r.bytes.val.length)
    (actual : Port6CK_Queries.read CheckpointBytes3Reader.raw r=ok (q,out)) :
    out.at.val=r.at.val+88 ∧ out.bytes=r.bytes := by
  unfold Port6CK_Queries.read at actual
'''
for i in range(22):
 r='r' if i==0 else f'r{i}'
 s+=f'''  obtain ⟨⟨b{i},r{i+1}⟩,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
  obtain ⟨contents,cursor,backing⟩ := CheckpointBytes4RawFields.raw_success 4#usize {r} r{i+1} b{i}
    (by change {r}.at.val+4≤{r}.bytes.val.length; omega) called
  change r{i+1}.at.val={r}.at.val+4 at cursor
  have room : r{i+1}.at.val+{4*(21-i)}≤r{i+1}.bytes.val.length := by rw [cursor,backing]; omega
  have cursor{i} : r{i+1}.at.val=r.at.val+{4*(i+1)} := by omega
  have backing{i} : r{i+1}.bytes=r.bytes := by first | exact backing | exact backing.trans backing{i-1}
  simp only [Aeneas.Std.uncurry] at actual
  obtain ⟨q{i},decoded,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
'''
s+='''  have finalReader := congrArg Prod.snd (Result.ok.inj actual)
  dsimp only at finalReader
  subst out
  exact ⟨cursor21,backing21⟩

#print axioms reached
end AspisR1.Port6CK_QueryFrame
end
'''
(P/'Port6CK_QueryFrame.lean').write_text(s)
