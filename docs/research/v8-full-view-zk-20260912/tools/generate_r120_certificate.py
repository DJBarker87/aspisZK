#!/usr/bin/env python3
"""Small, bounded fixed-weight certificate; no query recurrence is reduced.

The source exports literal weights. Independent arithmetic below checks the
signed bit map, three point tensors, sparse chord transpose, both channels,
all low blocks, and the 13x13 inverse before generating Lean leaves. Kernel
leaves retain the distinction between these fixed source-shaped expressions
and a universal Rust/source correspondence.
"""
import argparse, hashlib, json
from pathlib import Path

P=2147483647; HALF=(P+1)//2; QUARTER=pow(4,-1,P)

def tensor(z,r):
    v=1
    for i,x in enumerate(z):v=v*(x if (r>>(9-i))&1 else 1-x)%P
    return v

def points(z):
    carry=1; nxt=[0]*10
    for i in reversed(range(10)):
        nxt[i]=(z[i]+carry-2*z[i]*carry)%P;carry=carry*z[i]%P
    xor=z.copy();xor[6]=(1-z[6])%P;xor[7]=(1-z[7])%P
    return [z,nxt,xor]

def edges(j):
    row=j;bit=0;scale=1;out=[]
    while row&(1<<bit):
        row^=1<<bit;scale=scale*HALF%P;out.append((row,scale));bit+=1
    out.append((row|(1<<bit),scale));return out

def chord_column(j):
    d=j//2;out={}
    def add(i,v):out[i]=(out.get(i,0)+v)%P
    if j%2==0:
        add(2*d,7);add(2*d+1,-5)
        for r,w in edges(d):add(2*r,5*w)
    else:
        add(2*d,-5);add(2*d+1,7)
        for r,w in edges(d):
            add(2*r+1,5*w)
            for u,c in edges(r):add(2*u,5*w*c)
    return out

def coeff(w,d,s,k):
    a=sum(QUARTER*w[4*d+b] for b in range(4) if s+(4-b)%4==k)
    b=sum(QUARTER*w[4*d+b] for b in range(4) if (4-b)%4==k)
    return (a-pow(7,s,P)*b)%P

def observation(data,d,s,row):
    if row<3:
        w=data['point_weights'][row];return (w[4*d+s]-pow(7,s,P)*w[4*d])%P
    channel,k=(0,row-3) if row<10 else (1,row-10)
    return coeff(data['channel_weights'][channel],d,s,k)

def make(data,cert):
    assert data['source_only'] and not data['full_privacy']
    assert cert['constant_low_map'] and not cert['full_privacy'] and not cert['universal_root_theorem']
    assert data['z']==cert['z']==[1,1,2,3,4,0,2,3,4,2]
    assert cert['columns']==[0,1,2,3,4,5,12,13,14,15,16,17,23]
    assert cert['rows']==[1,2,3,4,5,6,7,8,10,11,12,13,15]
    assert len(data['order'])==len(data['inactive'])==131
    def base(j):return (j&1)|(((j>>1)&63)<<4)|(((j>>7)^7)<<1)
    order=[base(j) for j in range(1024)]
    order[127],order[1023]=order[1023],order[127]
    order[126],order[1021]=order[1021],order[126]
    assert order[:131]==data['order']
    for z,cw,ew in zip(points(data['z']),data['code_weights'],data['point_weights'],strict=True):
        assert len(cw)==131 and len(ew)==128
        assert cw==[(tensor(z,r)-(tensor(z,1023) if inactive else 0))%P for r,inactive in zip(order,data['inactive'])]
        for j in range(128):
            column=chord_column(j);assert max(column)<131
            assert ew[j]==sum(cw[r]*v for r,v in column.items())%P,(j,'chord')
    for j in range(128):
        e=[r[j] for r in data['point_weights']]
        assert data['channel_weights'][0][j]==(5*e[0]+25*e[1]+125*e[2])%P
        assert data['channel_weights'][1][j]==(25*e[1]+125*e[2]+5*pow(HALF,10,P)*chord_column(j).get(128,0))%P
    for d in range(23):
        for s in range(1,4):
            for row in range(17):assert observation(data,d,s,row)==observation(data,0,s,row)
    matrix=[[ (observation(data,23+c//3,c%3+1,r)-observation(data,0,c%3+1,r))%P
        for c in cert['columns']] for r in cert['rows']]
    assert matrix==cert['matrix']
    for i in range(13):
        for j in range(13):
            assert sum(matrix[i][k]*cert['inverse'][k][j] for k in range(13))%P==int(i==j)
    for array in [*data['code_weights'],*data['point_weights'],*data['channel_weights'],*matrix,*cert['inverse']]:
        assert all(type(x)==int and 0<=x<P for x in array)
    header='/- Generated R120 fixed-weight certificate. No query recurrence is evaluated. -/\n'
    ns='namespace AspisR19.TwoSwapWitness\nopen RootCertificate HighRepairInvariant ResidualModel AspisV8R17\nnoncomputable section\n'
    end='end\nend AspisR19.TwoSwapWitness\n';files={}
    s=header+'import AspisV8R19.RootCertificate\nimport AspisV8R19.HighRepairInvariant\nimport AspisV8R17.SourceChordTranspose\nimport Mathlib.Tactic.FinCases\n'+ns
    s+=f'def z (i : Fin 10) : M := ({data["z"]!r} : List M).getD i.val 0\n'
    s+=f'def orderValue (j : Nat) : Nat := ({data["order"]!r} : List Nat).getD j 0\n'
    s+=f'def inactiveValue (j : Nat) : Bool := ({str(data["inactive"]).lower()} : List Bool).getD j false\n'
    for name,values in [('codeValues',data['code_weights']),('pointValues',data['point_weights']),('channelValues',data['channel_weights']),('expectedMatrixValues',matrix),('inverseMatrixValues',cert['inverse'])]:
        s+=f'def {name} (i j : Nat) : M := ((({values!r} : List (List Nat)).getD i []).getD j 0 : M)\n'
    s+='''def codeFormula (which j : Nat) : M :=
  tensor (point z which) (orderValue j)-
    (if inactiveValue j then tensor (point z which) 1023 else 0)
def pointFormula (which r : Nat) : M :=
  sourceChordTranspose half (codeValues which) 7 5 (-5) r
def pointBlock (which : Nat) (i : Index 32) : M := pointValues which (4*i.1.val+i.2.val)
def channelBlock (which : Nat) (i : Index 32) : M := channelValues which (4*i.1.val+i.2.val)
def channelFormula (structured : Bool) (r : Nat) : M :=
  (if structured then 0 else 5*pointValues 0 r)+25*pointValues 1 r+125*pointValues 2 r+
    (if structured then 5*half^10*chordEntry half (7:M) 5 (-5) r 128 else 0)
def basisObservation (s : Fin 4) (d : Fin 32) (row : Nat) : M :=
  if row<3 then pointBlock row (d,s)-7^s.val*pointBlock row (d,0)
  else if row<10 then localCoeff (536870912:M) 7 d s (channelBlock 0) (row-3)
  else localCoeff (536870912:M) 7 d s (channelBlock 1) (row-10)
'''
    s+=f'def selectedColumn (j : Fin 13) : Nat := ({cert["columns"]!r} : List Nat).getD j.val 0\n'
    s+='''def degree (j : Fin 13) : Fin 32 := ⟨23+selectedColumn j/3, by fin_cases j <;> decide⟩
def slot (j : Fin 13) : Fin 4 := ⟨selectedColumn j%3+1, by omega⟩
def matrix : Matrix (Fin 13) (Fin 13) M := fun i j =>
  basisObservation (slot j) (degree j) (selectedRow i)-basisObservation (slot j) 0 (selectedRow i)
def expectedMatrix : Matrix (Fin 13) (Fin 13) M := fun i j => expectedMatrixValues i.val j.val
def inverseMatrix : Matrix (Fin 13) (Fin 13) M := fun i j => inverseMatrixValues i.val j.val
'''
    files['TwoSwapWitnessData.lean']=s+end
    for category,length,width,body in [
        ('Code',131,16,'codeFormula which.val (i.val+OFFSET)=codeValues which.val (i.val+OFFSET)'),
        ('Weights',128,16,'pointFormula which.val (i.val+OFFSET)=pointValues which.val (i.val+OFFSET)')]:
        for chunk,offset in enumerate(range(0,length,width)):
            count=min(width,length-offset);name=f'TwoSwap{category}Chunk{chunk:02}'
            text=header+'import AspisV8R19.TwoSwapWitnessData\n'+ns
            text+=f'theorem {category.lower()}_chunk{chunk} (which : Fin 3) (i : Fin {count}) :\n  '+body.replace('OFFSET',str(offset))+' := by\n  fin_cases which <;> fin_cases i <;> decide\n'
            text+=f'#print axioms {category.lower()}_chunk{chunk}\n'
            files[name+'.lean']=text+end
    text=header+'import AspisV8R19.TwoSwapWitnessData\n'+ns
    for which in range(3):
        text+=f'''theorem point_low{which} (d : Fin 23) (s : Fin 4) :
    pointValues {which} (4*d.val+s.val)=pointValues {which} s.val := by
  fin_cases d <;> fin_cases s <;> decide
#print axioms point_low{which}
'''
    for which in range(2):
        text+=f'''theorem channel_low{which} (d : Fin 23) (s : Fin 4) :
    channelValues {which} (4*d.val+s.val)=channelValues {which} s.val := by
  fin_cases d <;> fin_cases s <;> decide
#print axioms channel_low{which}
'''
    files['TwoSwapLowWeights.lean']=text+end
    for which in range(2):
        text=header+'import AspisV8R19.TwoSwapWitnessData\n'+ns
        text+=f'''theorem channel_formula{which} (r : Fin 128) :
    channelFormula {str(bool(which)).lower()} r.val=channelValues {which} r.val := by
  fin_cases r <;> decide
#print axioms channel_formula{which}
'''
        files[f'TwoSwapChannel{which}.lean']=text+end
    files['TwoSwapMatrixEntries.lean']=header+'import AspisV8R19.TwoSwapWitnessData\n'+ns+'''theorem matrix_entries : matrix=expectedMatrix := by
  funext i j
  fin_cases i <;> fin_cases j <;> decide
#print axioms matrix_entries
'''+end
    finish=header+'import AspisV8R19.TwoSwapMatrixEntries\nimport AspisV8R19.ResidualNonsingular\n'
    for i in range(13):
        name=f'TwoSwapInverseRow{i:02}'
        files[name+'.lean']=header+'import AspisV8R19.TwoSwapWitnessData\n'+ns+f'''theorem inverse_row{i} (j : Fin 13) : (expectedMatrix*inverseMatrix) {i} j=(1:Matrix (Fin 13) (Fin 13) M) {i} j := by
  fin_cases j <;> (rw [Matrix.mul_apply]; decide)
#print axioms inverse_row{i}
'''+end
        finish+=f'import AspisV8R19.{name}\n'
    finish+=ns+'''theorem right_inverse : expectedMatrix*inverseMatrix=1 := by
  funext i j
  fin_cases i
'''
    for i in range(13):finish+=f'  · exact inverse_row{i} j\n'
    finish+='''theorem model_det_ne_zero : matrix.det≠0 := by
  letI : Nontrivial M := ⟨⟨0,1,by decide⟩⟩
  rw [matrix_entries]
  exact ResidualNonsingular.right_inverse_det_ne_zero _ _ right_inverse
#print axioms right_inverse
#print axioms model_det_ne_zero
'''
    files['TwoSwapNonzero.lean']=finish+end
    finish=header+'import AspisV8R19.TwoSwapChannel0\nimport AspisV8R19.TwoSwapChannel1\n'
    for category,length in [('Code',131),('Weights',128)]:
        for chunk in range((length+15)//16):finish+=f'import AspisV8R19.TwoSwap{category}Chunk{chunk:02}\n'
    finish+=ns
    for category,length,lhs,rhs in [('code',131,'codeFormula','codeValues'),('weights',128,'pointFormula','pointValues')]:
        finish+=f'theorem {category}_correct (which : Fin 3) (j : Fin {length}) : {lhs} which.val j.val={rhs} which.val j.val := by\n'
        for chunk,offset in enumerate(range(0,length,16)):
            count=min(16,length-offset)
            if offset+count<length:
                finish+=f'  by_cases h{chunk} : j.val<{offset+count}\n  · '
            else:finish+='  '
            finish+=f'have h := {category}_chunk{chunk} which ⟨j.val-{offset},by omega⟩\n'
            indent='    'if offset+count<length else'  '
            finish+=indent+f'simpa only [Nat.sub_add_cancel (show {offset}≤j.val by omega)] using h\n'
        finish+=f'#print axioms {category}_correct\n'
    files['TwoSwapFixedWeights.lean']=finish+end
    return files

def main():
    p=argparse.ArgumentParser();p.add_argument('--input',type=Path,required=True);p.add_argument('--output',type=Path,required=True);p.add_argument('--check',action='store_true');p.add_argument('--extend',action='store_true');a=p.parse_args()
    weights=a.input/'source-weights.json';cert=a.input/'high_code_support_pivot_check.json'
    files=make(json.loads(weights.read_text()),json.loads(cert.read_text()))
    assert a.output.is_dir()
    for name,s in files.items():
        dest=a.output/name
        if a.check or (a.extend and dest.exists()):assert dest.read_text()==s,name
        else:assert not dest.exists(),dest;dest.write_text(s)
    print(json.dumps({'mode':'check'if a.check else'write','files':len(files),'weights_sha256':hashlib.sha256(weights.read_bytes()).hexdigest(),'certificate_sha256':hashlib.sha256(cert.read_bytes()).hexdigest(),'source_shaped_fixed_model':True,'rust_refinement':False,'universal_root_theorem':False,'full_privacy':False}))

if __name__=='__main__':main()
