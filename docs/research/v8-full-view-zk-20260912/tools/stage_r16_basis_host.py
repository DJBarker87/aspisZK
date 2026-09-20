#!/usr/bin/env python3
"""New research profile: common encoding transport and inverse-dual verifier.

Never mutate the pinned stage or call this a production privacy repair.
The dense terminal path is deliberate: old structured weights do not commute
with this transport. Existing verification and corruption controls remain.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
from reconstruct_generated_inputs import EXPERIMENTS, one_replace


def replace_body(text, signature, body):
    assert text.count(signature) == 1, signature
    start = text.index('{', text.index(signature))
    depth = 1
    end = start + 1
    # These pinned methods have no braces inside string literals/comments.
    while depth:
        depth += (text[end] == '{') - (text[end] == '}')
        end += 1
    return text[:start+1] + '\n' + body + '\n    ' + text[end-1:]


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--repo', type=Path, required=True)
    p.add_argument('--output', type=Path, required=True)
    args = p.parse_args()
    out = args.output.resolve()
    subprocess.run([sys.executable, str(Path(__file__).with_name('stage_r15_host.py')),
                    '--repo', str(args.repo.resolve()), '--output', str(out)], check=True)
    metadata = json.loads((out / 'r15-stage.json').read_text())
    assert '--cfg v8_structured' in metadata['rustflags']
    assert '--cfg v8_performance_sbf' not in metadata['rustflags']
    edits = []

    def edit(name, transform):
        path = out / EXPERIMENTS / name
        before = path.read_bytes()
        after = transform(before.decode()).encode()
        path.write_bytes(after)
        edits.append(dict(path=str(EXPERIMENTS / name),
            before_sha256=hashlib.sha256(before).hexdigest(), after_sha256=hashlib.sha256(after).hexdigest()))

    def witness(s):
        s = one_replace(s, 'two_outputs(leaf,dig(900))', 'two_outputs(leaf,leaf)', 'same-public fixture')
        return one_replace(s, 'pair_leaf:pair,selected_second:false,',
            'pair_leaf:pair,selected_second:std::env::var("ASPIS_R16_SELECTED_SECOND").as_deref()==Ok("1"),', 'witness selector')

    edit('recovered_witness.rs', witness)
    edit('relation_callback.rs', lambda s: one_replace(s, 'use corelib::{',
        'mod r16_basis_transport;\nuse corelib::{', 'shared candidate transport'))

    def performance(s):
        s = one_replace(s, 'enc.encode_c1_message(m).unwrap()',
            'enc.encode_c1_message(&crate::r16_basis_transport::transport().forward(m)).unwrap()', 'C1 transport')
        return one_replace(s, 'enc.encode_c2_message(m).unwrap()',
            'enc.encode_c2_message(&crate::r16_basis_transport::transport().forward(m)).unwrap()', 'C2 transport')

    edit('performance.rs', performance)

    def payment(s):
        s = one_replace(s, 'fn ood(m:&[K],p:Point)->K{',
            'fn ood(m:&[K],p:Point)->K{let mapped=crate::r16_basis_transport::transport().forward(m);let m=mapped.as_slice();', 'OOD uses encoded polynomial')
        return one_replace(s, 'fn start(binding:&[u8;32],a:&f::Tree)->(Transcript,K,K){let mut t=Transcript::new(hash);',
            'fn start(binding:&[u8;32],a:&f::Tree)->(Transcript,K,K){let mut t=Transcript::new(hash);t.absorb(label::PROFILE,b"AV8/R16/basis89-dual-dense/research-v1");', 'new research transcript profile')

    edit('payment_extraction.rs', payment)
    edit('performance_verifier.rs', lambda s: one_replace(s,
        'let mut t=Transcript::new(hash);',
        'let mut t=Transcript::new(hash);t.absorb(label::PROFILE,b"AV8/R16/basis89-dual-dense/research-v1");',
        'verifier uses the same new research transcript profile'))
    edit('inactive_row_binding.rs', lambda s: one_replace(s,
        'let original=materialize_original(&d.z,d.scales);',
        'let original=crate::r16_basis_transport::transport().dual(&materialize_original(&d.z,d.scales));', 'prover inverse-dual weights'))

    def structured(s):
        s = one_replace(s, 'let original=materialize_original(&z,scales);',
            'let original=crate::r16_basis_transport::transport().dual(&materialize_original(&z,scales));', 'controls use inverse-dual weights')
        s = one_replace(s, 'transpose(&materialize_original(&d.z,d.scales),d.abc)',
            'transpose(&crate::r16_basis_transport::transport().dual(&materialize_original(&d.z,d.scales)),d.abc)',
            'independent dense terminal reference uses inverse-dual weights')
        s = replace_body(s, 'fn entry_pair(&self,index:usize)->[K;2]',
            '        assert!(index==1 || index==2); [self.entry(0),self.entry(index)]')
        s = one_replace(s, 'pub(in super::super) fn entry(&self,index:usize)->K {',
            '''pub(in super::super) fn entry(&self,index:usize)->K {
        let map=crate::r16_basis_transport::transport();
        let r=map.order[index];let v=self.base_entry(r);
        if r!=1023 && map.inactive[r]{v.sub(self.base_entry(1023))}else{v}
    }
    fn base_entry(&self,index:usize)->K {''', 'verifier inverse-dual entry')
        s = replace_body(s, 'pub(in super::super) fn terminal(&self,alpha:[K;4])->[K;4]',
            '''        let original:Vec<K>=(0..1024).map(|i|self.entry(i)).collect();
        let mut weights=WeightAccumulator::empty(10);
        weights.add_dense(transpose(&original,self.abc)).unwrap();
        for a in alpha{weights.fold_deferred_relation_arity4(a);}
        core::array::from_fn(|i|weights.weight_at(i as u32))''')
        s = one_replace(s, 'AV8/functional/three-MLE-grouped64/chord/v2',
            'AV8/R16/functional/inverse-dual-dense/chord/v1', 'functional profile separation')
        s = one_replace(s, 'desc.extend([20,22,10,4,4,use_x as u8]);',
            '''desc.extend([20,22,10,4,4,use_x as u8]);
    let map=crate::r16_basis_transport::transport();
    for &r in &map.order{desc.extend((r as u16).to_le_bytes());}
    for &inactive in &map.inactive{desc.push(inactive as u8);}''', 'bind exact source-derived transport')
        return s

    edit('structured_weights.rs', structured)
    module = Path(__file__).with_name('r16_basis_transport.rs').read_bytes()
    (out / EXPERIMENTS / 'r16_basis_transport.rs').write_bytes(module)
    metadata.update(instrumentation=edits, diagnostic_only=True, privacy_proved=False,
        transport_sha256=hashlib.sha256(module).hexdigest(),
        scope='R16 candidate encoding/dual/OOD transport, dense verifier terminal, same-public fixture; ordinary SHA and nonce; not production')
    (out / 'r16-stage.json').write_text(json.dumps(metadata, indent=2) + '\n')
    print(json.dumps({'stage': str(out), 'changes': edits}, indent=2))


if __name__ == '__main__':
    main()
