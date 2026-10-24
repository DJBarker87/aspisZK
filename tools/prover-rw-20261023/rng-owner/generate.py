from pathlib import Path
import hashlib,json
D=Path(__file__).resolve().parent;P=D.parent/'rng-preflight'
s=(P/'prototype/lib.rs').read_text().split('#[cfg(test)]')[0]
r=(P/'prototype/runtime.rs').read_text();old=r[r.index('    pub fn old('):r.index('\nfn view(')].replace('Recorder','Tape')
s+='\nimpl From<u8> for StateOnlyAttemptEntropyError { fn from(e:u8)->Self { Self::Os(e) } }\n'
s+='''
impl Tape {
    fn draw(&mut self, bytes: &mut [u8;64]) -> Result<(),u8> {
        assert!(self.used < self.replies.len());
        let (block, result) = self.replies[self.used];
        self.used += 1;
        *bytes = block;
        result
    }
}
impl StateOnlyAttemptSecrets {
'''+old+'''
pub fn old_owner(nonce:[u8;32], mut tape:Tape) -> (Tape,Result<StateOnlyAttemptSecrets,StateOnlyAttemptEntropyError>) {
    let status=StateOnlyAttemptSecrets::old(nonce,&mut tape);
    (tape,status)
}
'''
(D/'prototype').mkdir(exist_ok=True);(D/'prototype/lib.rs').write_text(s)
(D/'prototype/Cargo.toml').write_text((P/'prototype/Cargo.toml').read_text().replace('rng-preflight','rng-owner'))
(D/'prototype/Cargo.lock').write_text((P/'prototype/Cargo.lock').read_text().replace('rng-preflight','rng-owner'))
(D/'source-map.json').write_text(json.dumps({'base':'ece5baabbc9c975d631aae8d5ca716e28ad4f268','old':'same exact old routine as runtime-binding, substituting Tape for Recorder; native fill becomes Tape.draw','provider':'Tape.draw copies actual indexed block/status and advances used; borrowed interface exposes state separately from Result','new':'verbatim cap16 prototype with owned Draw64','source_sha256':hashlib.sha256(s.encode()).hexdigest(),'native_error_layout':False,'no_pure_world_equality_assumed':True},indent=2)+'\n')
