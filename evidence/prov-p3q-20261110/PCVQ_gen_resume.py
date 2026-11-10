#!/usr/bin/env python3
# Generates PRVEq_Resume_<tag>.lean: symbolic-execution proof of resume_sim (item 1), walking the fresh VTop resume in execution order.
import sys
tag=sys.argv[1]
head=open('PCVQ_head.lean').read().replace('PCVQ_Resume','PCVQ_Resume'+tag)
T=[]
def B(n='_'): T.append(f"  refine sim_bind _ _ _ (fun {n} _ => ?_)")
def P(a,b): T.append("  refine sim_bind _ _ _ (fun p _ => ?_)"); T.append(f"  obtain ⟨{a}, {b}⟩ := p")
def I(): T.append("  refine sim_ite _ (fun _ => ?_) (fun _ => ?_)"); T.append("  · rfl")
def TR(n): T.append(f"  refine sim_try _ _ _ (fun {n} => ?_) (fun _ => rfl)")
T.append("  refine sim_bind _ _ _ (fun i1 hi1 => ?_)")
T.append("  refine sim_ite _ (fun _ => ?_) (fun hc => ?_)"); T.append("  · rfl")
B('s'); B('b'); I(); B('i2'); B('i3'); I(); B('i4'); I(); B('i5'); I(); B('s1'); B('i6'); P('b1','it'); I()
T.append("  have hlen : 32 ≤ (Slice.len bytes).val := by")
T.append("    have e : Slice.len bytes = i1 := by\n      rw [bne_iff_ne] at hc; exact not_not.mp hc")
T.append("    rw [e]; exact sizeBound v i1 hi1")
T.append("  rw [sub32 _ hlen]")
B('end1'); B('s2'); B('s3'); B('a'); B('b2'); I()
B('s4'); B('s5'); B('a1'); B('b3'); I()
B('s6'); B('s7'); B('s8'); B('s9'); B('a2')
T.append("  unfold Port4A_NativeReader.tail")
B('b4'); I()
P('state','r'); P('a3','r1'); P('a4','r2')
for i,(a,b) in enumerate([('r3','r4'),('r5','r6'),('r7','r8'),('r9','r10'),('r11','r12')]):
    P(a,b); TR('val' if i==0 else f'val{i}')
for j in range(22):
    P(f'a{5+j}',f'r{13+j}'); B(f'i{8+j}')
B('r35'); TR('_u')
B('r36'); TR('val5'); T.append("  obtain ⟨semantic_alpha, at1⟩ := val5")
for i,(a,b) in enumerate([('r37','r38'),('r39','r40'),('r41','r42'),('r43','r44'),('r45','r46'),('r47','r48'),('r49','r50')]):
    P(a,b); TR(f'val{6+i}')
B('i30'); B('q'); B('r52'); TR('val13')
B('r53'); TR('val14'); T.append("  obtain ⟨weights, at2⟩ := val14")
I(); B('i31'); T.append("  rfl")
body='''
theorem sub32 (n : Std.Usize) (h : 32 ≤ n.val) :
    (n - 32#usize : Result Std.Usize) = lift (Usize.wrapping_sub n 32#usize) := by
  obtain ⟨out, run, value, _⟩ := WP.spec_imp_exists (UScalar.sub_spec (x := n) (y := 32#usize) (by scalar_tac))
  have same : out = Usize.wrapping_sub n 32#usize := by
    apply UScalar.eq_of_val_eq
    have capacity : n.val < UScalar.size .Usize := by
      have := n.hBounds; simpa [UScalar.size_def] using this
    have c32 : 32 < UScalar.size .Usize := by rw [UScalar.size_def]; scalar_tac
    have e1 : (32#usize).val = 32 := rfl
    rw [Usize.wrapping_sub_val_eq, value, e1]
    have : n.val + (UScalar.size .Usize - 32) = (n.val - 32) + UScalar.size .Usize := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  rw [run, same]; rfl

set_option pp.deepTerms.threshold 6 in
set_option maxRecDepth 20000 in
theorem resume_sim (x : Ext) (ops : AspisR1Stage2.ResumeOps) (L : Leaves x ops)
    (sizeBound : ∀ v n, ops.checkpointSize v = ok n → 32 ≤ n.val)
    {H : Type} (D : aspis_core.digest.Digest32 H) (bytes proof public1 : Slice Std.U8)
    (v : transport.Variant) (hash : H) :
    Sim (verifier.resume x D bytes proof public1 v hash)
      (Port4A_NativeReader.resume ops (VTop_Checkpoint.digest D) bytes proof public1 v hash) := by
  unfold verifier.resume Port4A_NativeReader.resume
  simp only [L.size, L.tag, L.ne, L.any, L.raw, L.k, L.e, L.validate, L.sem, L.weights, L.final, L.zero, L.filled,
    core.cmp.impls.PartialEqShared.ne, AspisR1Stage2.slicePartialEq, Slice.Insts.CoreCmpPartialEqArray,
    VTop_Checkpoint.digest]
'''
open(f'PRVEq_Resume_{tag}.lean','w').write(head+body+"\n".join(T)+f"\n#print axioms resume_sim\nend PCVQ_Resume{tag}\n")
