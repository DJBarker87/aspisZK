#!/usr/bin/env python3
import argparse, hashlib, re
from pathlib import Path
P = 2147483647
GEN = (2, 1268011823)
ADAPTER_SHA = 'f1c1765883a09cc9d9ec926127efbd3810f9f60cf5c77893d35b633e5288bb3f'

def reverse_bits(width, value):
    out = 0
    for i in range(width): out = (out << 1) | ((value >> i) & 1)
    return out

def cmul(x, y):
    return ((x[0]*y[0] % P + P - x[1]*y[1] % P) % P,
            (x[0]*y[1] + x[1]*y[0]) % P)

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--table', choices=['A','B'], required=True)
    ap.add_argument('--chunk', type=int, choices=range(16), required=True)
    ap.add_argument('--adapter', type=Path, required=True)
    ap.add_argument('--output', type=Path, required=True)
    ap.add_argument('--check', action='store_true')
    a=ap.parse_args()
    raw=a.adapter.read_bytes()
    got=hashlib.sha256(raw).hexdigest()
    assert got == ADAPTER_SHA, (got, ADAPTER_SHA)
    text=raw.decode()
    cname=f'TABLE_{a.table}_chunk_{a.chunk:02d}'
    line=next(x for x in text.splitlines() if x.startswith(f'def fast_domain.{cname}'))
    pairs=[tuple(map(int,x)) for x in re.findall(r'\((\d+)#u32, (\d+)#u32\)',line)]
    assert len(pairs)==32, (cname,len(pairs))
    offset=a.chunk*32
    power_name='leftExponent' if a.table=='A' else 'rightExponent'
    exps=[(2**10+2**21*reverse_bits(9,offset+i)) if a.table=='A'
          else 2**12*reverse_bits(9,offset+i) for i in range(32)]
    # Independently compute source values and reject a mismatched table before emitting Lean.
    vals={0:(1,0)}
    needed={0}
    for n in exps:
        while n:
            needed.add(n); n//=2
    for n in sorted(needed):
        if n==0: continue
        y=vals[n//2]
        vals[n]=cmul(y,y) if n%2==0 else cmul(cmul(y,y),GEN)
    assert [vals[n] for n in exps]==pairs, (cname, [(i,exps[i],vals[exps[i]],pairs[i]) for i in range(32) if vals[exps[i]]!=pairs[i]][:1])
    ns=f'R17Table{a.table}Chunk{a.chunk:02d}Certificate'
    out=[]
    out += ['import R17MinimalReverseBits','import R17TableExponentDomainBridge','import R17TableBasePowerProbe','import R17TableBasePowerBridge','import Lean.Elab.Tactic.Omega','', 'set_option autoImplicit false','', f'namespace {ns}','open R17MinimalReverseBits','open R17TableExponentDomainBridge','open R17TableBasePowerProbe','']
    out += ['def toNatC (x : R17TableBasePowerProbe.C) :','    R17TableBasePowerBridge.NatC := ⟨x.re, x.im⟩','', 'theorem toNatC_cmul (x y : R17TableBasePowerProbe.C) :','    toNatC (R17TableBasePowerProbe.cmul x y) =','      R17TableBasePowerBridge.natMul (toNatC x) (toNatC y) := rfl','', 'theorem fastPow_succ (x : R17TableBasePowerProbe.C) (k : Nat) :','    R17TableBasePowerProbe.fastPow x (k + 1) =','      let y := R17TableBasePowerProbe.fastPow x ((k + 1) / 2)','      if (k + 1) % 2 == 0 then R17TableBasePowerProbe.cmul y y','      else R17TableBasePowerProbe.cmul (R17TableBasePowerProbe.cmul y y) x := by','  simp [R17TableBasePowerProbe.fastPow]','']
    out += ['theorem fastPow_toNatPow (x : R17TableBasePowerProbe.C) (n : Nat) :','    toNatC (R17TableBasePowerProbe.fastPow x n) =','      R17TableBasePowerBridge.natPow (toNatC x) n := by','  induction n using Nat.strong_induction_on with','  | h n ih =>','    cases n with','    | zero => simp [R17TableBasePowerProbe.fastPow, R17TableBasePowerBridge.natPow,','        R17TableBasePowerProbe.cone, R17TableBasePowerBridge.oneN, toNatC]','    | succ k =>','      have hm : (k + 1) / 2 < k + 1 := by omega','      have him := ih ((k + 1) / 2) hm','      simp only [R17TableBasePowerProbe.fastPow, R17TableBasePowerBridge.natPow]','      by_cases hparity : (k + 1) % 2 == 0','      · simp only [toNatC_cmul, if_pos hparity, him]','      · simp only [toNatC_cmul, if_neg hparity, him]','','theorem fastPow_decode_zPow (n : Nat) :','    R17TableBasePowerBridge.decode','        (toNatC (R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen n)) =','      R17TableBasePowerBridge.zPow','        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen)) n := by','  rw [fastPow_toNatPow]','  exact R17TableBasePowerBridge.natPow_decode_zPow (toNatC R17TableBasePowerProbe.gen) n','']
    for n in sorted(needed):
        x,y=vals[n]
        if n==0: proof='by simp [R17TableBasePowerProbe.fastPow, R17TableBasePowerProbe.cone]'
        else:
            m=n//2
            proof=f'''by
  conv_lhs => rw [fastPow_succ]
  rw [power_{m}]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]'''
        out += [f'theorem power_{n} : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen {n} = ⟨{x}, {y}⟩ := {proof}','']
    for i,((x,y),e) in enumerate(zip(pairs,exps)):
        idx=offset+i
        out += [f'theorem entry_{i:02d} :','    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen',f'      (R17TableExponentDomainBridge.{power_name} {idx}) = ⟨{x}, {y}⟩ := by',f'  have hexp : R17TableExponentDomainBridge.{power_name} {idx} = {e} := by','    norm_num [R17TableExponentDomainBridge.'+power_name+', R17MinimalReverseBits.reverseBits]','  rw [hexp]',f'  exact power_{e}','']
        out += [f'theorem entry_{i:02d}_zPow :','    R17TableBasePowerBridge.decode','        (toNatC (⟨'+f'{x}, {y}'+ '⟩ : R17TableBasePowerProbe.C)) =','      R17TableBasePowerBridge.zPow','        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))',f'        (R17TableExponentDomainBridge.{power_name} {idx}) := by',f'  rw [← entry_{i:02d}]','  exact fastPow_decode_zPow _','']
    for i in range(32): out += [f'#print axioms entry_{i:02d}',f'#print axioms entry_{i:02d}_zPow']
    out += ['',f'end {ns}','']
    generated='\n'.join(out)
    if a.check:
        assert a.output.exists(), 'output source absent'
        assert a.output.read_text()==generated, 'generated source stale'
        # Recheck exact statement ordering and literal outputs.
        for i,(x,y) in enumerate(pairs):
            needle=(f'theorem entry_{i:02d} :\n    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen\n'
                    f'      (R17TableExponentDomainBridge.{power_name} {offset+i}) = ⟨{x}, {y}⟩')
            assert needle in generated, (i, needle)
        print(f'checked {cname}: source SHA {got}; 32 ordered literal entries; generated SHA {hashlib.sha256(generated.encode()).hexdigest()}')
    else:
        a.output.write_text(generated)
        print(f'generated {cname} from source SHA {got}; pairs=32 powers={len(needed)} outputSHA={hashlib.sha256(generated.encode()).hexdigest()}')
if __name__=='__main__': main()
