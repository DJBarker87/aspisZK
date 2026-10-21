from pathlib import Path
import hashlib,json,sys
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013'
p=B/'evidence/s7-kani-20261021/extraction/generated/S7OwnedP6/Funs.lean';s=p.read_text();a=s.index('def prefixes_owned\n');b=s.index('partial_fixpoint',a)+len('partial_fixpoint');original=s[a:b]
body=original.replace('aspis_core.field.M31','U32').replace('U32.mul','AspisR1Qm31ArithmeticProbe.field.M31.mul')
header='''import S7Kani2AccumulatorLoop
import ExtractedCurrentReducer

/- Literal emitted prefix loop with the actual already-proved frozen M31
multiply. Bounds cover the entire 110-entry geometry allocation. -/
set_option autoImplicit false
namespace S7Kani2PrefixLoop
open Aeneas Aeneas.Std Result
open AspisV8R17.RawReducer

'''
tail='''
def wordMul (x y : U32) : U32 :=
  UScalar.ofNatCore ((x.val*y.val)%P) (by
    have hm := Nat.mod_lt (x.val*y.val) (show 0<P by decide)
    have hp : P<2^32 := by decide
    change (x.val*y.val)%P<2^32
    exact Nat.lt_trans hm hp)

theorem multiply_word (x y : U32) :
    AspisR1Qm31ArithmeticProbe.field.M31.mul x y=ok (wordMul x y) := by
  obtain ⟨z,hz,hvalue,_⟩ := AspisR1.ExtractedCurrentReducer.current_mul_mod x y
  have he : z=wordMul x y := UScalar.eq_of_val_eq hvalue
  simpa only [he] using hz

def model : List U32 → List U32 → U32 → List U32 × U32
 | [],prefixes,product => (prefixes,product)
 | x::xs,prefixes,product => model xs (prefixes++[product]) (wordMul product x)

/-- Complete total refinement of the actual emitted prefix loop. No
multiplication, push or step-equality hypothesis is assumed. -/
theorem prefixes_refines (flat : alloc.vec.Vec U32) (prefixes : alloc.vec.Vec U32)
    (product : U32) (index : Usize) (fuel : Nat)
    (hflat : flat.val.length≤110) (remaining : index.val+fuel=flat.val.length)
    (capacity : prefixes.val.length+fuel≤110) :
    ∃ prefixesOut productOut,
      prefixes_owned flat prefixes product index=ok (flat,prefixesOut,productOut) ∧
      (prefixesOut.val,productOut)=model (flat.val.drop index.val) prefixes.val product := by
  induction fuel generalizing index prefixes product with
  | zero =>
      have hstop : index ≥ alloc.vec.Vec.len flat := by scalar_tac
      refine ⟨prefixes,product,?_,?_⟩
      · rw [prefixes_owned]
        simp only [hstop,if_pos]
      · have hd : flat.val.drop index.val=[] := List.drop_eq_nil_iff.mpr (by omega)
        simp only [hd,model]
  | succ fuel ih =>
      have hb : index.val<flat.val.length := by omega
      have running : ¬ index ≥ alloc.vec.Vec.len flat := by scalar_tac
      have hcap : prefixes.val.length<Usize.max := by
        have hm : 110<Usize.max := by scalar_tac
        omega
      obtain ⟨prefixes1,hpush,hprefixes1⟩ := WP.spec_imp_exists
        (alloc.vec.Vec.push_spec prefixes product hcap)
      obtain ⟨x,hread,hx⟩ := WP.spec_imp_exists
        (alloc.vec.Vec.index_usize_spec flat index hb)
      have hr : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice U32)
          flat index=ok x := hread
      obtain ⟨index1,hinc,hindex1⟩ := S7Kani2AccumulatorLoop.increment index (by omega)
      have hc1 : prefixes1.val.length+fuel≤110 := by
        rw [hprefixes1,List.length_append]
        simp only [List.length_singleton]
        omega
      obtain ⟨out,finalProduct,hrun,hvalue⟩ := ih prefixes1 (wordMul product x) index1
        (by omega) hc1
      refine ⟨out,finalProduct,?_,?_⟩
      · rw [prefixes_owned]
        simp only [running,if_false,hpush,hr,multiply_word,hinc,bind_tc_ok]
        exact hrun
      · have hd : flat.val.drop index.val = x::flat.val.drop (index.val+1) := by
          simpa only [←hx] using (List.drop_eq_getElem_cons (l:=flat.val) hb)
        rw [hd,model]
        simpa only [hindex1,hprefixes1] using hvalue

#print axioms multiply_word
#print axioms prefixes_refines
end S7Kani2PrefixLoop
'''
text=header+body+'\n'+tail;out=B/'lean/S7Kani2PrefixLoop.lean'
if '--check' in sys.argv:assert out.read_text()==text
else:out.write_text(text)
(B/'evidence/s7-kani2-20261021/prefix-binding.json').write_text(json.dumps(dict(source=str(p.relative_to(R)),source_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),declaration_sha256=hashlib.sha256(original.encode()).hexdigest(),edits='Exact U32 carrier alias; opaque M31.mul instantiated by the exact frozen source arithmetic probe definition, whose source hash matches frozen field.rs.'),indent=2)+'\n')
