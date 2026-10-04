#!/usr/bin/env python3
"""Generate/check the SCC-6 full left-inverse row aggregation module."""
import argparse,hashlib
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
CERT=ROOT/".r21-scratch/r724-h1-left-inverse-certificate/evidence/attempt-2-success/certificate.json"
DEP747=ROOT/".r21-scratch/r747-joint-block39-preflight/R747JointBlock39Preflight.lean"
DEP749=ROOT/".r21-scratch/r749-joint-block39-row28/R749JointBlock39Row28.lean"
CHUNKS=ROOT/".r21-scratch/r749-joint-block39-row28/chunks"
OUT=Path(__file__).with_name("R751JointBlock39Inverse.lean")
PINS={
 'certificate.json':'d170dc15f81b0aac68da6cb9291e9907ad72e1738cf3a6b6fd7faf9e32a951f4',
 'R747JointBlock39Preflight.lean':'0d3d110e4bfc42a5769dd0e5c4c77c4f464f4e7be6c4769644ec84fa6557a78a',
 'R749JointBlock39Row28.lean':'c1c50f7b7f09ea78a13b72a0e8d632dd28728f8ebc1041d1afdb2228b9fa2996',
 'R750JointBlock39Rows01.lean':'a2b17b84d57e4f35fed24e822ca50186cd177a4dee0ce8f3c33b16030fa5ef52',
 'R750JointBlock39Rows02.lean':'e081bf94f1d5a11349eebc263c859d5f301d71bfcd359fc29ee990a87eab447d',
 'R750JointBlock39Rows03.lean':'c17098337197039a35d78107b962b15acbec975a4d85f620822886d2337619c9',
 'R750JointBlock39Rows04.lean':'69efc42b1da9920faec4fd19615fc46741443ac697da4445e651b538d5dc8e2b',
 'R750JointBlock39Rows05.lean':'82d583f97f68eb5bea7af6268ac0136525450851051ad1a213b9d026af8b9cb7',
 'R750JointBlock39Rows06.lean':'1fa09dfd70e4e986a7afc6bc89436d48584fe6b3eb6318df5f2a5229928b72ee',
 'R750JointBlock39Rows07.lean':'1fc64ab3c2d6d1890f0fc6b123d057019c340a85b1257207493fd340947b8347',
 'R750JointBlock39Rows08.lean':'d8e905c5f88318f9fbe2d7b413383abffd1ba8b57fb5396ea640dfff662934af',
 'R750JointBlock39Rows09.lean':'28a42d58697f211d07ca1e4fbe83b37ca2ca9965628c2a5f6f1f6bd74d3c77df',
 'R750JointBlock39Rows10.lean':'390e538b4560bdc2a424a251e272cbd7f24f4a6678f17516629ed5e048dbe1d3',
}
ROW_MODULE={0:(1,0),1:(1,1),2:(1,2),3:(2,3),4:(2,4),5:(2,5),6:(2,6),7:(3,7),8:(3,8),9:(3,9),10:(3,10),11:(4,11),12:(4,12),13:(4,13),14:(4,14),15:(5,15),16:(5,16),17:(5,17),18:(5,18),19:(6,19),20:(6,20),21:(6,21),22:(6,22),23:(7,23),24:(7,24),25:(7,25),26:(7,26),27:(8,27),28:None,29:(8,29),30:(8,30),31:(8,31),32:(9,32),33:(9,33),34:(9,34),35:(9,35),36:(10,36),37:(10,37),38:(1,38)}

def build():
    imports=['AspisV8R19.R747JointBlock39Preflight','AspisV8R19.R749JointBlock39Row28']
    imports += [f'AspisV8R19.R750JointBlock39Rows{i:02d}' for i in range(1,11)]
    lines=['''/- Aggregates the independently checked 39 rows of the SCC-6 candidate B*A.
This is a finite candidate-block result; it does not bind the matrix to source
execution or close the privacy/security argument. -/''']
    lines += [f'import {m}' for m in imports]
    lines += ['import Mathlib.LinearAlgebra.Matrix.NonsingularInverse','',
      'namespace R751JointBlock39Inverse','open R747JointBlock39Preflight','',
      'local instance : Fact (1 < 2147483647) := ⟨by decide⟩','',
      'theorem left_inverse : B * A = 1 := by','  ext i j','  fin_cases i']
    for r in range(39):
        if r==28:
            expr='R749JointBlock39Row28.row28 j'
        else:
            chunk,row=ROW_MODULE[r]
            expr=f'R750JointBlock39Rows{chunk:02d}.row_{row} j'
        lines.append(f'  · exact {expr}')
    lines += ['', '#print axioms left_inverse','',
      'theorem determinant_nonzero : Matrix.det A ≠ 0 :=','  Matrix.det_ne_zero_of_left_inverse left_inverse','',
      '#print axioms determinant_nonzero','',
      'end R751JointBlock39Inverse','']
    return '\n'.join(lines)

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');args=ap.parse_args()
    sources={'certificate.json':CERT,'R747JointBlock39Preflight.lean':DEP747,'R749JointBlock39Row28.lean':DEP749}
    for name in [f'R750JointBlock39Rows{i:02d}.lean' for i in range(1,11)]: sources[name]=CHUNKS/name
    for name,path in sources.items():
        h=hashlib.sha256(path.read_bytes()).hexdigest()
        if h!=PINS[name]:raise SystemExit(f'{name} hash mismatch {h}')
    text=build()
    if args.check:
        if not OUT.exists() or OUT.read_text()!=text:raise SystemExit('aggregate source mismatch/missing')
    else: OUT.write_text(text)
    print(f'check={"ok" if args.check else "written"} rows=39 certificate_sha256={PINS["certificate.json"]} source_sha256={hashlib.sha256(text.encode()).hexdigest()}')
if __name__=='__main__':main()
