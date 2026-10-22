from pathlib import Path
s='''import CheckpointBytes4Ops

set_option autoImplicit false
noncomputable section
namespace AspisR1.CheckpointBytes4SemanticFields
open Aeneas Aeneas.Std Result
open AspisR1Stage2 CheckpointBytes4Sections CheckpointBytes4Ops

private theorem cons_success (read : ReadK) (n : Nat) (r next last : verifier.Reader)
    (x : K) (xs : List K)
    (first : read r = ok (.Ok x,next))
    (tail : readList read n next = ok (.Ok (xs,last))) :
    readList read (n+1) r = ok (.Ok (x::xs,last)) := by
  rw [readList,first]
  change (do
    let rest ← readList read n next
    match rest with
    | .Err e => ok (core.result.Result.Err e)
    | .Ok (ys,finish) => ok (core.result.Result.Ok (x::ys,finish))) = _
  rw [tail]
  rfl

/-- Every output of the source's ten unrolled reads comes from the matching
ordered sequential decoder, with the exact final cursor. -/
theorem semantic_fields (read : ReadK) (bytes : Slice U8) (start finish : Usize)
    (values : Array K 10#usize)
    (success : semanticUsing read bytes start = ok (.Ok (values,finish))) :
    ∃ last : verifier.Reader,
      readList read 10 ⟨bytes,start⟩ = ok (.Ok (values.val,last)) ∧ last.at = finish := by
  unfold semanticUsing at success
  simp only [withK] at success
'''
indent='  '
h='success'
for i in range(10):
 s+=indent+f'obtain ⟨⟨value{i},r{i+1}⟩,read{i},tail{i}⟩ := OraclePortCkptAbiTry.bind_success _ _ _ {h}\n'
 s+=indent+f'cases value{i} with\n'+indent+f'| Err e => cases tail{i}\n'+indent+f'| Ok x{i} =>\n'
 indent+='  '
 h=f'tail{i}'
s+=indent+f'have eq := core.result.Result.Ok.inj (Result.ok.inj {h})\n'
s+=indent+'have hv := congrArg Prod.fst eq\n'+indent+'have hc := congrArg Prod.snd eq\n'+indent+'dsimp only at hv hc\n'+indent+'subst values finish\n'
s+=indent+'refine ⟨r10,?_,rfl⟩\n'
s+=indent+'change readList read 10 ⟨bytes,start⟩ = ok (.Ok (['+','.join(f'x{i}' for i in range(10))+'],r10))\n'
s+=indent+'exact '+''.join(f'cons_success read {9-i} _ _ _ _ _ read{i} (' for i in range(10))+'rfl'+')'*10+'\n'
s+='''
/-- The C5 scalar reader is consumed on the real section, rather than an
assumed equality of semantic output arrays. -/
theorem semantic_c5_fields (bytes : Slice U8) (start finish : Usize)
    (values : Array K 10#usize)
    (success : readSemanticAlpha bytes start = ok (.Ok (values,finish))) :
    ∃ last : verifier.Reader,
      readList c5ReadK 10 ⟨bytes,start⟩ = ok (.Ok (values.val,last)) ∧ last.at = finish := by
  obtain ⟨last,run,cursor⟩ := semantic_fields CheckpointBytes3Reader.readK bytes start finish values success
  rw [read_list_identification] at run
  exact ⟨last,run,cursor⟩

#print axioms cons_success
#print axioms semantic_fields
#print axioms semantic_c5_fields
end AspisR1.CheckpointBytes4SemanticFields
end
'''
Path('docs/research/100bit-spend-path-20261013/lean/CheckpointBytes4SemanticFields.lean').write_text(s)
