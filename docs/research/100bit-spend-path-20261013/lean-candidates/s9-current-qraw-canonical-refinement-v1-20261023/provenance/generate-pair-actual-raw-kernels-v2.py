from pathlib import Path
import json,hashlib
W=Path('/tmp/pair-actual-raw-kernels-v2');(W/'sources').mkdir(parents=True,exist_ok=True)
old=Path('/Users/dominic/ZK/docs/research/100bit-spend-path-20261013/lean-candidates/s5-current-repin-20261020/namespace-rebase-v1/sources/AspisR1CanonicalQRawUnified/Funs.lean');new=Path('/tmp/pair-h5-raw-source-model-v1/sources/AspisR1S9ActualRawCutV1/Funs.lean');o=old.read_text();n=new.read_text()
os=o.index('def canonical.Q.raw\n');ob=o.index('  := do\n',os)+len('  := do\n');ot=o.index('  let i ← c * g\n',ob);op=o[ob:ot];tailo=o[ot:];tailo=tailo[:tailo.index('\n/--')].rstrip()+'\n'
ns=n.index('def fast_pairing.canonical.Q.raw\n');nb=n.index('  := do\n',ns)+len('  := do\n');nt=n.index('  let i16 ← lift (Std.U64.wrapping_mul c g)\n',nb);np=n[nb:nt];tailn=n[nt:];tailn=tailn[:tailn.index('\n/--')].rstrip()+'\n'
qualo=lambda s:s.replace('canonical.','AspisR1CanonicalQRawUnified.canonical.');qualn=lambda s:s.replace('fast_pairing.canonical.','AspisR1S9ActualRawCutV1.fast_pairing.canonical.')
s='''import AspisR1S9ActualRawCutV1.Funs
import QRawSourceForwardTotalityV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9ActualRawKernelsV1
abbrev A4 := Array U32 4#usize
abbrev R4 := Array U64 4#usize
abbrev cv := core.convert.num.FromU64U32.from
abbrev Kernel := U64 → U64 → U64 → U64 → U64 → U64 → U64 → U64 → Result R4
/-- Exact retained source tail; irreducibility seals symbolic arithmetic during input specialization. -/
@[irreducible] def checkedKernel (a1 b c d e f g h : U64) : Result R4 := do
'''+qualo(tailo)+'''
/-- Exact actual release source tail; no arithmetic operator edits. -/
@[irreducible] def actualKernel (a b c d e f g h : U64) : Result R4 := do
'''+qualn(tailn)+'''
/-- Exact retained model input prefix with its arithmetic continuation explicit. -/
def checkedPrefix (kernel : Kernel) (self rhs : A4) : Result R4 := do
'''+qualo(op)+'''  kernel a1 b c d e f g h
/-- Exact actual direct-read prefix with its arithmetic continuation explicit. -/
def actualPrefix (kernel : Kernel) (self rhs : A4) : Result R4 := do
'''+qualn(np)+'''  kernel a b c d e f g h

theorem checked_raw_factor (self rhs : A4) :
    AspisR1CanonicalQRawUnified.canonical.Q.raw self rhs =
      checkedPrefix checkedKernel self rhs := by
  unfold AspisR1CanonicalQRawUnified.canonical.Q.raw checkedPrefix checkedKernel
  rfl

theorem actual_raw_factor (self rhs : A4) :
    AspisR1S9ActualRawCutV1.fast_pairing.canonical.Q.raw self rhs =
      actualPrefix actualKernel self rhs := by
  unfold AspisR1S9ActualRawCutV1.fast_pairing.canonical.Q.raw actualPrefix actualKernel
  rfl

private theorem ix0 {A : Type} (a b c d : A) : Array.index_usize (Array.make 4#usize [a,b,c,d]) 0#usize = .ok a := rfl
private theorem ix1 {A : Type} (a b c d : A) : Array.index_usize (Array.make 4#usize [a,b,c,d]) 1#usize = .ok b := rfl
private theorem ix2 {A : Type} (a b c d : A) : Array.index_usize (Array.make 4#usize [a,b,c,d]) 2#usize = .ok c := rfl
private theorem ix3 {A : Type} (a b c d : A) : Array.index_usize (Array.make 4#usize [a,b,c,d]) 3#usize = .ok d := rfl

private theorem map_left_four (a b c d : U32) :
    core.array.Array.map
      AspisR1CanonicalQRawUnified.canonical.Q.raw.closure.Insts.CoreOpsFunctionFnMutTupleU32U64
      (Array.make 4#usize [a,b,c,d]) () = .ok (Array.make 4#usize [cv a,cv b,cv c,cv d]) := by
  obtain ⟨mapped,hm⟩ := AspisR1CanonicalQRawUnified.Proof.raw_left_map_total (Array.make 4#usize [a,b,c,d])
  have hv := AspisR1QRawActualC0V2.closure_zero_map_val_local _ mapped hm
  have he : mapped=Array.make 4#usize [cv a,cv b,cv c,cv d] := by
    apply Subtype.ext
    simpa only [Array.make,List.map_cons,List.map_nil] using hv
  exact he ▸ hm
private theorem map_right_four (a b c d : U32) :
    core.array.Array.map
      AspisR1CanonicalQRawUnified.canonical.Q.raw.closure_1.Insts.CoreOpsFunctionFnMutTupleU32U64
      (Array.make 4#usize [a,b,c,d]) () = .ok (Array.make 4#usize [cv a,cv b,cv c,cv d]) := by
  obtain ⟨mapped,hm⟩ := AspisR1CanonicalQRawUnified.Proof.raw_right_map_total (Array.make 4#usize [a,b,c,d])
  have hv := AspisR1QRawActualC0V2.closure_one_map_val_local _ mapped hm
  have he : mapped=Array.make 4#usize [cv a,cv b,cv c,cv d] := by
    apply Subtype.ext
    simpa only [Array.make,List.map_cons,List.map_nil] using hv
  exact he ▸ hm

/-- Only input words are specialized; the checked arithmetic kernel stays sealed. -/
theorem checked_raw_literal_prefix (a b c d e f g h : U32) :
    AspisR1CanonicalQRawUnified.canonical.Q.raw
      (Array.make 4#usize [a,b,c,d]) (Array.make 4#usize [e,f,g,h]) =
      checkedKernel (cv a) (cv b) (cv c) (cv d) (cv e) (cv f) (cv g) (cv h) := by
  rw [checked_raw_factor]
  unfold checkedPrefix
  rw [map_left_four]
  simp only [bind_tc_ok,ix0,ix1,ix2,ix3]
  rw [map_right_four]
  simp only [bind_tc_ok,ix0,ix1,ix2,ix3]

/-- Only actual direct reads/casts are specialized; no arithmetic DAG unfolds. -/
theorem actual_raw_literal_prefix (a b c d e f g h : U32) :
    AspisR1S9ActualRawCutV1.fast_pairing.canonical.Q.raw
      (Array.make 4#usize [a,b,c,d]) (Array.make 4#usize [e,f,g,h]) =
      actualKernel (cv a) (cv b) (cv c) (cv d) (cv e) (cv f) (cv g) (cv h) := by
  rw [actual_raw_factor]
  unfold actualPrefix
  simp only [bind_tc_ok,ix0,ix1,ix2,ix3,lift]

#print axioms checked_raw_factor
#print axioms actual_raw_factor
#print axioms checked_raw_literal_prefix
#print axioms actual_raw_literal_prefix
end AspisR1S9ActualRawKernelsV1
'''
p=W/'sources/S9ActualRawKernelsV1.lean';p.write_text(s);sha=lambda b:hashlib.sha256(b).hexdigest();(W/'source-tail-pins.json').write_text(json.dumps({'checked_source_sha256':sha(old.read_bytes()),'actual_source_sha256':sha(new.read_bytes()),'checked_prefix_sha256':sha(qualo(op).encode()),'actual_prefix_sha256':sha(qualn(np).encode()),'checked_tail_sha256':sha(qualo(tailo).encode()),'actual_tail_sha256':sha(qualn(tailn).encode()),'adaptation':'Exact prefix/tail spans, identifier qualification only. Source binder a1 retained in checked helper. Irreducibility is proof normalization only; generic source factorizations prove actual correspondence before word specialization.','retained_failure':'v1 specialized complete raw arithmetic DAG then rfl reached existing M4400 limit. No capincrease; v2 introduces explicit prefix/kernel separation and seals arithmetic.'},indent=2)+'\n');print(sha(s.encode()))
