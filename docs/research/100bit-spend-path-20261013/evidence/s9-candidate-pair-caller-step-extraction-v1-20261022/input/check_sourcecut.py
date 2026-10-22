from pathlib import Path
import hashlib, json
ROOT=Path(__file__).resolve().parent
CUT=ROOT/'source-cut'
PINS=json.loads((ROOT/'sourcecut-pins.json').read_text())
sha=lambda b: hashlib.sha256(b).hexdigest()
def function(text, marker):
    start=text.index(marker); brace=text.index('{',start); depth=0
    for i in range(brace,len(text)):
        if text[i]=='{': depth+=1
        elif text[i]=='}':
            depth-=1
            if depth==0:return text[start:i+1]
    raise AssertionError(f'unterminated: {marker}')
def norm(s): return ''.join(line.strip() for line in s.splitlines())
candidate=(ROOT/'pins/candidate-weights.rs').read_text()
frozen=(ROOT/'pins/frozen-weights.rs').read_text()
assert sha((ROOT/'pins/candidate-weights.rs').read_bytes())==PINS['candidate_weights_sha256']
assert sha((ROOT/'pins/frozen-weights.rs').read_bytes())==PINS['frozen_weights_sha256']
cp=function(candidate,'pub fn pair('); fp=function(frozen,'pub fn pair(')
assert cp==fp and sha(cp.encode())==PINS['candidate_pair_body_sha256']
cf=function(candidate,'pub fn field('); ff=function(frozen,'pub fn field(')
assert cf==ff and sha(cf.encode())==PINS['candidate_field_body_sha256']
call='let libra=if self.variant==Variant::S2 {factored_s2_libra_weights(&ap0,&ap1,self.extra)}else{twofold_libra_weights(&low,self.extra)};\n            for j in 0..4 {parts[4]=parts[4].add(field(f,j).mul(libra[j]));}'
assert norm(call) in norm(cp)
lib=(CUT/'lib.rs').read_text()
proj=function(lib,'pub fn pair_s2_libra_parts_projection(')
assert norm(call) in norm(proj)
assert 'pub fn pair_step_root(' in lib
# The original helper-only harness is a frozen base; only projection/root insertion is permitted.
assert sha((ROOT/'base-lib.rs').read_bytes())==PINS['base_lib_sha256']
base=(ROOT/'base-lib.rs').read_text()
projection='''    pub fn pair_s2_libra_parts_projection(\n        &self, f: &[u8], ap0: [E; 4], ap1: [E; 4], low: [E; 16], mut parts: [E; 7],\n    ) -> [E; 7] {\n        let libra=if self.variant==Variant::S2 {factored_s2_libra_weights(&ap0,&ap1,self.extra)}else{twofold_libra_weights(&low,self.extra)};\n        for j in 0..4 {parts[4]=parts[4].add(field(f,j).mul(libra[j]));}\n        parts\n    }\n'''
shim=''' // Extraction-only caller-step root; this exposes exactly the local helper\n // call and four-cell `parts[4]` consumer, not the enclosing pair function.\n pub fn pair_step_root(w:&Weights,f:&[u8],ap0:[E;4],ap1:[E;4],low:[E;16],parts:[E;7])->[E;7]{\n  w.pair_s2_libra_parts_projection(f,ap0,ap1,low,parts)\n }\n'''
expected=base.replace('    #[inline(never)]\n    pub fn pair(&self,alpha:&[E],f:&[u8],kappa:E)->Result<E,Error> {',projection+'    #[inline(never)]\n    pub fn pair(&self,alpha:&[E],f:&[u8],kappa:E)->Result<E,Error> {',1)
expected=expected.replace(' // Extraction-only root shim: Charon cannot use an inherent method as --start-from.\n',shim+' // Extraction-only root shim: Charon cannot use an inherent method as --start-from.\n',1)
assert lib==expected, 'unexpected harness edit beyond exact projection/root addition'
for name,expected_sha in PINS['source_cut_files'].items(): assert sha((CUT/name).read_bytes())==expected_sha,name
print('PASS: candidate/frozen pair bodies are byte-identical and pinned')
print('PASS: candidate/frozen field decoder bodies are byte-identical and pinned')
print('PASS: helper call and four-cell parts update are copied at the caller slice')
print('PASS: source-cut differs from frozen helper harness only by the projected method and extraction root')
