#!/usr/bin/env python3
from pathlib import Path
import hashlib,json
P=Path(__file__).resolve().parent
base=(P/"input/frozen-weights.rs").read_bytes()
candidate=(P/"input/candidate-weights.rs").read_bytes()
pins=json.loads((P/"input/source-pins.json").read_text())
assert hashlib.sha256(base).hexdigest()==pins["frozen_source_sha256"]
assert hashlib.sha256(candidate).hexdigest()==pins["candidate_source_sha256"]
# The deterministic generator used to produce the candidate is included; its
# exact transformations are checked against unique original byte blocks.
text=base.decode(); needle="    #[inline(never)]\n    pub fn pair(&self,alpha:&[E],f:&[u8],kappa:E)->Result<E,Error> {\n"
helper=Path(P/"input/helpers.txt").read_text()+needle
assert text.count(needle)==1
text=text.replace(needle,helper,1)
repls=[
("                let mut pair=crate::fast_pairing::EbyKDot::new();\n                for j in 0..n {pair.push(field(f,j),scratch[j]).map_err(|_|Error::Parse)?;}\n                parts[kind]=scale.mul(pair.finish());\n", "                let pair=Self::push_byte_products_row(f,&scratch,n)?;\n                parts[kind]=scale.mul(pair);\n"),
("            for s in 0..4 {\n                let mut dot=crate::fast_pairing::EbyKDot::new();\n                for j in 0..16 {\n                    dot.push(field(f,16*s+j),common[j]).map_err(|_|Error::Parse)?;\n                }\n                partials[s]=dot.finish();\n            }\n", "            for s in 0..4 { partials[s]=Self::push_byte_products_partial(f,&common,s)?; }\n"),
("                let mut high=crate::fast_pairing::EbyKDot::new();\n                for s in 0..4 {\n                    high.push(partials[s],self.factors[k][4][s]).map_err(|_|Error::Parse)?;\n                }\n                let scale=Self::scalar_factor(&self.factors[k][0],&ap0)\n                    .mul(Self::scalar_factor(&self.factors[k][1],&ap1));\n                parts[kind]=scale.mul(high.finish());\n", "                let high=Self::push_byte_products_high(&partials,&self.factors[k][4])?;\n                let scale=Self::scalar_factor(&self.factors[k][0],&ap0)\n                    .mul(Self::scalar_factor(&self.factors[k][1],&ap1));\n                parts[kind]=scale.mul(high);\n")]
for old,new in repls:
 old=old.encode().decode("unicode_escape"); new=new.encode().decode("unicode_escape")
 assert text.count(old)==1,old
 text=text.replace(old,new,1)
assert text.encode()==candidate
print("PASS: candidate is exactly frozen weights.rs plus the three declared loop-to-helper substitutions")
