#!/usr/bin/env python3
"""Render bounded-step Pratt and fixture checks; no huge ordinary powers.
Data generation is untrusted; Lean checks all arithmetic and prime certificates.
"""
import json, pathlib, sys
ROOT = pathlib.Path(__file__).resolve().parents[2]
HERE = pathlib.Path(__file__).resolve().parent

def render(data):
    out=['import JHt_PrattCore','set_option autoImplicit false','namespace AspisR1.JHt_Prime','open JHt_BinaryModPow JHt_PrattCore', 'attribute [local irreducible] modPow']
    for row in data:
        p,a,fs=row['p'],row['a'],row['factors']
        if p < 1000:
            out += [f'theorem prime_{p} : Nat.Prime {p} := by norm_num', f'#print axioms prime_{p}']
            continue
        assert __import__('math').prod(fs)==p-1
        exps=[p-1]+[(p-1)//q for q in sorted(set(fs))]
        for i,e in enumerate(exps):
            val=pow(a,e,p)
            assert val==1 if i==0 else val!=1
            out += [f'theorem exp_{p}_{i} : modPow {a} {e} {p} 256 = {val} := by decide +kernel',f'#print axioms exp_{p}_{i}']
        qs='['+', '.join(map(str,fs))+']'
        out += [f'theorem prime_{p} : Nat.Prime {p} := by',f'  apply certificate {p} {a} 256 (by decide) {qs}',
                '  · intro q hq', '    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq',
                '    rcases hq with '+ ' | '.join(['rfl']*len(fs)),
                '    all_goals first | '+ ' | '.join(f'exact prime_{q}' for q in sorted(set(fs))),
                '  · decide', f'  · exact exp_{p}_0', '  · intro q hq',
                '    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq',
                '    rcases hq with '+ ' | '.join(['rfl']*len(fs))]
        for q in fs:
            i=sorted(set(fs)).index(q)+1
            val=pow(a,(p-1)//q,p)
            out += ['    · intro heq',f"      have hh := (ZMod.natCast_eq_natCast_iff' (modPow {a} (({p}-1)/{q}) {p} 256) 1 {p}).mp heq", f'      rw [exp_{p}_{i}] at hh',f'      exact (by decide : {val} % {p} ≠ 1 % {p}) hh']
        out += [f'#print axioms prime_{p}']
    out += ['end AspisR1.JHt_Prime','']
    return '\n'.join(out)

def render_cells(data):
    p=2**255-19
    d=37095705934669439343138083508754565189542113879843219016388785533085940283555
    out=['import JHt_BinaryModPow','set_option autoImplicit false','namespace AspisR1.JHt_Residues', 'open JHt_BinaryModPow','attribute [local irreducible] modPow']
    for row in data:
        name,y,u,v,vi,r=(row[k] for k in ['name','y','u','v','inverse','ratio'])
        assert y==(int.from_bytes(bytes(row['bytes']),'little')%2**255)%p
        assert u==(y*y-1)%p and v==(d*y*y+1)%p
        assert vi==pow(v,p-2,p) and r==u*vi%p
        assert v!=0 and u!=0 and pow(r,(p-1)//2,p)==p-1
        out += [f'namespace {name}', f'def y : Nat := {y}',f'def inverse : Nat := modPow {v} {p-2} {p} 256', f'def ratio : Nat := {r}',
            f'theorem inverseValue : inverse = {vi} := by decide +kernel','#print axioms inverseValue',
            f'theorem inverseCheck : ({d} * y*y + 1) * inverse % {p} = 1 := by', '  rw [inverseValue]', '  decide +kernel','#print axioms inverseCheck',
            f'theorem ratioCheck : (y*y + {p} - 1) * inverse % {p} = ratio := by', '  rw [inverseValue]', '  decide +kernel','#print axioms ratioCheck',
            f'theorem euler : modPow ratio {p//2} {p} 256 = {p-1} := by decide +kernel','#print axioms euler', f'end {name}']
    return '\n'.join(out+['end AspisR1.JHt_Residues',''])

if __name__=='__main__':
    data=json.loads((HERE/'JHt_PRATT.json').read_text())
    target=ROOT/'lean/JHt_Prime.lean'
    s=render(data)
    cells=render_cells(json.loads((HERE/'JHt_CELLS.json').read_text()))
    cells_target=ROOT/'lean/JHt_Residues.lean'
    if '--check' in sys.argv:
        assert target.read_text()==s
        assert cells_target.read_text()==cells
        print('Pratt generator check passed: '+str(len(data))+' prime nodes')
    else:
        target.write_text(s)
        cells_target.write_text(cells)
