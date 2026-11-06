from NLQ_formal import *
import base64

def native(a,target):
    frozen=json.loads(lzma.decompress((E.parent/'sdk-borrow-20261109/NLF_FROZEN_INPUTS.json.xz').read_bytes()))
    lib=base64.b64decode(frozen['NLF_src/programs/r1-cost-probe/src/lib.rs']).decode()
    lib='#![cfg_attr(kani,feature(allocator_api))]\n'+lib+'\n#[cfg(kani)]\n#[path="NLQ_native.rs"]\nmod NLQ_native;\n'
    patch=frozen['NLF_KMX_copy_stubs.patch']
    files={'NLQ_src/programs/r1-cost-probe/src/lib.rs':lib,
      'NLQ_src/programs/r1-cost-probe/src/NLQ_native.rs':''.join(l[1:] for l in (E/'NLQ_NATIVE.patch').read_text().split('+++ b/programs/r1-cost-probe/src/NLQ_native.rs\n',1)[1].split('--- ',1)[0].splitlines(True) if l.startswith('+')),
      'NLQ_gate.py':(E/'NLQ_gate.py').read_text(),'NLQ_expected_KMX.patch':patch}
    env=json.loads((E.parent/'sdk-borrow-20261109/NLF_K044.json').read_text())['env']
    env.update(TMPDIR=B+'/NLQ_tmp',CARGO_TARGET_DIR=B+'/NLQ_target',CARGO_NET_OFFLINE='true')
    cmd=['/home/dombarker/.cargo/bin/cargo-kani','kani','--manifest-path',B+'/NLQ_src/programs/r1-cost-probe/Cargo.toml','--target-dir',B+'/NLQ_target','--features','pool-adapter,private-leaf-salts','--lib','-j','1','-Z','unstable-options','-Z','function-contracts','-Z','stubbing','--harness-timeout','90s','--exact','--harness',target,'--output-format','terse']
    config=dict(native_command=cmd,root_package='aspis-r1-cost-probe-program')
    # The unchanged scope runner runs the owned strict gate. Its config is a source input.
    adapter=base64.b64decode(frozen['NLF_src/programs/r1-cost-probe/src/r1_pool_adapter.rs']).decode()
    files['NLQ_src/programs/r1-cost-probe/src/r1_pool_adapter.rs']=adapter+'\n#[cfg(kani)]\n#[path="NLQ_adapter.rs"]\npub(crate) mod NLQ_adapter;\n'
    files['NLQ_src/programs/r1-cost-probe/src/NLQ_adapter.rs']=''.join(l[1:] for l in (E/'NLQ_NATIVE.patch').read_text().split('+++ b/programs/r1-cost-probe/src/NLQ_adapter.rs\n',1)[1].splitlines(True) if l.startswith('+'))
    files['NLQ_native_config.json']=json.dumps(dict(attempt=a,**config))
    rc=run(a,'kani',target,command=['python3','NLQ_gate.py','NLQ_native_config.json'],extra=files,env_extra=env)
    log=lzma.decompress((E/a/'stdout.log.xz').read_bytes()).decode()
    assert 'Checking harness '+target in log, 'STOP queue: compile/preflight rejection; inspect before next launch'
    assert 'VERIFICATION:-' in log, 'STOP queue: no final native verdict; isolate before another launch'
    return rc
if __name__=='__main__':native(*sys.argv[1:])
