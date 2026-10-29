"""Generate an OWNED normalized x86 control projection, not extractor output.
The hardware shuffle+round pair is kept as one instruction group: its unused
upper lanes differ from soft::sha256swap. No equality of those vectors is asserted.
"""
from pathlib import Path
import re,hashlib,json
P=Path('docs/research/v8-r0-zk-20261009/lean/R1Z');s=(P/'PV_RDB2E_FallbackBlock.lean').read_text();body=s[s.index('def sha_fallback_reference.sha256_digest_block_u32'):s.index('/-- [pv_cblib_source::sha_fallback_reference::extracted_block]')]
statements=re.split(r'(?=^  let )',body,flags=re.M);out=[];i=0;pairs=0
while i<len(statements):
 a=statements[i]
 if '← sha_fallback_reference.sha256swap' in a:
  m=re.search(r'let (\w+) ← sha_fallback_reference.sha256swap (\w+)',a);b=statements[i+1];assert m and 'sha_fallback_reference.sha256_digest_round_x2' in b
  b=b.replace('sha_fallback_reference.sha256_digest_round_x2','intr.shuffleRound');b=re.sub(r'\b'+m[1]+r'\b',m[2],b);out.append(b);i+=2;pairs+=1
 else:out.append(a);i+=1
assert pairs==16
b=body.replace('def sha_fallback_reference.sha256_digest_block_u32','def wordBlock (intr : Intrinsics)').replace('sha_fallback_reference.add','intr.add').replace('sha_fallback_reference.sha256_digest_round_x2','intr.round').replace('sha_fallback_reference.schedule','schedule intr')
header='''import R1Z.PV_RDB2E_FallbackBlockTotal
namespace R1Z.PV_RDB2F_ShaNi
open Aeneas Aeneas.Std Result PV_CBL_FallbackBlock
set_option autoImplicit false
abbrev Vec := Array U32 4#usize
abbrev State := Array U32 8#usize
abbrev Block := Array U8 64#usize
abbrev Words := Array U32 16#usize
/-- High-first lane encoding. shuffleRound is exactly shuffle(0x0E) then rnds2;
its unused upper lanes need not equal software swap's upper lanes. -/
structure Intrinsics where
  add : Vec → Vec → Result Vec
  round : Vec → Vec → Vec → Result Vec
  shuffleRound : Vec → Vec → Vec → Result Vec
  msg1 : Vec → Vec → Result Vec
  align4 : Vec → Vec → Result Vec
  msg2 : Vec → Vec → Result Vec
  pack : State → Result State
  load : Block → Result Words
  unpack : State → Result State

def referenceShuffleRound (a b t : Vec) : Result Vec := do
  let shuffled ← sha_fallback_reference.sha256swap t
  sha_fallback_reference.sha256_digest_round_x2 a b shuffled

/-- ONE explicit conditional instruction-semantics hypothesis, pending owner
item 3. This is neither a trust-list field nor a proved native instruction law.
pack/unpack include the listed loadu/shuffle/align/blend/store lane conversions;
load is loadu plus byte shuffle MASK. All equations concern local instruction
groups, never the desired digest/finalizer conclusion. -/
structure SHA_NI_IntrinsicsSemantics (intr : Intrinsics) : Prop where
  add : intr.add=sha_fallback_reference.add
  round : intr.round=sha_fallback_reference.sha256_digest_round_x2
  shuffleRound : intr.shuffleRound=referenceShuffleRound
  msg1 : intr.msg1=sha_fallback_reference.sha256msg1
  align4 : intr.align4=sha_fallback_reference.sha256load
  msg2 : intr.msg2=sha_fallback_reference.sha256msg2
  pack : ∀ s, intr.pack s=ok s
  load : intr.load=PV_CBL_ShaBytes.sha_load64
  unpack : ∀ s, intr.unpack s=ok s

def schedule (intr : Intrinsics) (v0 v1 v2 v3 : Vec) : Result Vec := do
  let t1 ← intr.msg1 v0 v1
  let t2 ← intr.align4 v2 v3
  let t3 ← intr.add t1 t2
  intr.msg2 t3 v3

theorem schedule_semantics (intr : Intrinsics) (h : SHA_NI_IntrinsicsSemantics intr) :
    schedule intr=sha_fallback_reference.schedule := by
  funext v0 v1 v2 v3
  simp only [schedule,sha_fallback_reference.schedule,h.msg1,h.align4,h.add,h.msg2]

'''
# ShaBytes is supplied by SHAModel, not by the standalone word block.
header=header.replace('import R1Z.PV_RDB2E_FallbackBlockTotal','import R1Z.PV_RDB2E_FallbackBlockTotal\nimport R1Z.PV_RDB2D_SHAModel')
footer='''
theorem word_block_semantics (intr : Intrinsics) (h : SHA_NI_IntrinsicsSemantics intr)
    (state : State) (words : Words) :
    wordBlock intr state words=sha_fallback_reference.extracted_block state words := by
  rcases intr with ⟨add,round,shuffleRound,msg1,align4,msg2,pack,load,unpack⟩
  rcases h with ⟨ha,hr,hs,hm1,hl,hm2,hp,hload,hu⟩
  dsimp only at ha hr hm1 hl hm2
  subst add
  subst round
  subst msg1
  subst align4
  subst msg2
  unfold wordBlock sha_fallback_reference.extracted_block
    sha_fallback_reference.sha256_digest_block_u32
  repeat' (apply (Aeneas.Std.bind_eq_iff _ _ _).mpr; intro next hnext)
  rfl

/-- Explicit local justification for replacing each source shuffle+round pair
by the software lane-normalized pair. Upper unused lanes are not equated. -/
theorem shuffle_pair_semantics (intr : Intrinsics) (h : SHA_NI_IntrinsicsSemantics intr)
    (a b t : Vec) : intr.shuffleRound a b t=referenceShuffleRound a b t := by
  rw [h.shuffleRound]


#print axioms schedule_semantics
#print axioms word_block_semantics
#print axioms shuffle_pair_semantics
end R1Z.PV_RDB2F_ShaNi
'''
(P/'PV_RDB2F_ShaNi.lean').write_text(header+b+footer)
Path('evidence/pv-rdb2f-20261029/shani-projection.json').write_text(json.dumps(dict(classification='owned normalized control projection; CONDITIONAL instruction groups; no extraction claim',source_sha256=hashlib.sha256(s.encode()).hexdigest(),shuffle_round_groups=pairs,condition='SHA_NI_IntrinsicsSemantics',pending='owner item 3',T_changed=False),indent=2)+'\n')
