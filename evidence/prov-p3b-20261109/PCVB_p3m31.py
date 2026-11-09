#!/usr/bin/env python3
"""PCVB_p3m31.py IN_PRVEq.lean OUT_PRVEq_P3.lean
Phase P3b, M31.mul. Reads a P2f PRVEq equality file. (1) inserts the generic arithmetic lemmas (PCVB_m31_lemmas.lean)
before the gate namespace; (2) replaces the M31.mul PRV-OBLIGATION comment by a proof of fresh = gate for ALL inputs
(case split on the two guards of the gate body; fast branch: PCVB_M31.fast_chain, which needs only the guards);
(3) turns every other semantic PRV-OBLIGATION whose fresh body calls an equality-proved callee into the same S2 shape the
generator uses (delta; simp only [callee equalities]; rfl)."""
import sys,re
inp,out=sys.argv[1:3]
here=__import__('pathlib').Path(__file__).resolve().parent
lem=(here/'PCVB_m31_lemmas.lean').read_text()
R23='--r23' in sys.argv
if R23: lem+= '\n'+(here/'PCVB_r23_lemmas.lean').read_text()
lem=lem.replace('namespace PCVB_M31','namespace PCVB_M31',1)
src=open(inp).read()
# 1. lemma insertion right after 'noncomputable section'
m=re.search(r'^noncomputable section\n',src,re.M)
src=src[:m.end()]+'\n/- PCVB generic arithmetic lemmas (phase P3b, M31.mul): see PCVB_m31_lemmas.lean -/\n'+lem+'\n'+src[m.end():]
OB=re.compile(r'/- PRV-OBLIGATION \(semantic; P3\): (\S+) : @(\S+) = @(\S+)\n   last probe error: [^\n]*-/\n')
def mulproof(eq,fq,gq):
    assert eq.endswith('M31.mul') and gq.endswith('field.M31.mul')
    gns=gq[:-len('M31.mul')]       # '<ns>.field.'
    gp=gns+'P'; gr=gns+'reduce_u64'
    pre=eq[:-len('M31.mul')]
    fr=fq[:-len('M31.mul')]+'reduce_u64'
    redeq=pre+'reduce_u64'
    return f'''set_option maxHeartbeats 200000 in
/-- P3b: fresh M31.mul = gate M31.mul as functions on ALL inputs. The gate takes a fast path only when both operands are < P;
    every other input runs the same product-then-reduce_u64 chain as fresh. -/
theorem {eq} : @{fq} = @{gq} := by
  funext self rhs
  have hr : @{fr} = @{gr} := {redeq}
  have hP : ({gp} : Std.U32).val = 2147483647 := by
    unfold {gp}; rfl
  unfold {fq} {gq}
  rw [hr]
  by_cases h1 : self < {gp}
  · by_cases h2 : rhs < {gp}
    · rw [if_pos h1, if_pos h2]
      exact PCVB_M31.fast_chain {gp} hP {gr} (fun x => rfl) self rhs h1 h2
    · rw [if_pos h1, if_neg h2]
      try rfl
  · rw [if_neg h1]
    try rfl
#print axioms {eq}
'''
thms=re.findall(r'^theorem (PRVEq\.\S+) :',src,re.M)
def short(n,pre): return n[len(pre):]
res=[];pos=0;count=0;newly=[]
out_s='';last=0
# pre = common prefix up to the module label
first=OB.search(src)
assert first,'no obligation'
for mo in OB.finditer(src):
    eq,fq,gq=mo.groups()
    if eq.endswith('field.M31.mul'):
        txt=mulproof(eq,fq,gq); newly.append(eq)
        if R23:
            gns_=gq[:-len('M31.mul')]
            R23NAME=eq[:-len('M31.mul')]+'r23_gate'
            txt+=f'''
/-- P3b: the gate-only helper r23_product_u32_bounded is the plain checked u64 product (both guards only select an
    equal-valued u32 round trip). -/
theorem {R23NAME} : ∀ l r, {gns_}r23_product_u32_bounded l r = l * r := fun l r => PCVB_R23.r23_eq l r
#print axioms {R23NAME}
'''
        pre=eq[:-len('field.M31.mul')]
        if eq.endswith('aspis_core.field.M31.mul'): pre=eq[:-len('aspis_core.field.M31.mul')]
    else:
        # callee equalities proved earlier in the file (defined before this position)
        before=src[:mo.start()]
        done=re.findall(r'^theorem (PRVEq\.\S+) :',before,re.M)+newly
        # the fresh body of this def
        sh=fq.split('PRVFresh_',1)[1].split('.',1)[1]
        mb=re.search(r'^def '+re.escape(sh)+r'\b(.*?)(?=^/--|^end PRVFresh_)',before.split('end PRVFresh_')[0] if False else src,re.S|re.M)
        body=mb.group(1) if mb else ''
        cal=[]
        for d in done:
            s_=d[len(pre):] if d.startswith(pre) else None
            if s_ and s_!=sh and re.search(r'(?<![\w.])'+re.escape(s_)+r'(?![\w.])',body): cal.append(d)
        if R23: cal=cal+[R23NAME]
        simp=f'; try simp only [{", ".join(cal)}]' if cal else ''
        txt=f'''set_option maxHeartbeats 200000 in
theorem {eq} : @{fq} = @{gq} := by
  (trace "PRV-S2 {eq}"; delta {fq} {gq}{simp}; try rfl; done)
#print axioms {eq}
'''
    if not eq.endswith('field.M31.mul'): newly.append(eq)
    out_s+=src[last:mo.start()]+txt
    last=mo.end()
    count+=1
out_s+=src[last:]
open(out,'w').write(out_s)
print(inp,'->',out,'obligations replaced',count)
