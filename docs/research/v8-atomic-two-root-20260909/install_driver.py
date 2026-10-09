#!/usr/bin/env python3
import hashlib, pathlib
ex=pathlib.Path(__file__).resolve().parent
root=ex.parents[2]
assert str(root)=='/home/dombarker/project-offloads/aspis-v8-atomic-two-root-20260909' and not (root/'.git').exists()
p=root/'results/v7-pair-forest-combined-rejection-litesvm-20260828/harness/src/main.rs'
s=p.read_text()
assert hashlib.sha256(p.read_bytes()).hexdigest()=='264cab184d72b27e8945235041c9f74993bdc6462165f729ab95276850a85957'
prefix='#[path="../../../../docs/research/v8-atomic-two-root-20260909/driver.rs"]\nmod atomic;\n'
needle='    let instruction_account_count = instruction.accounts.len();'
assert s.count(needle)==1
s=prefix+s.replace(needle,'''    if env::var_os("ASPIS_ATOMIC_EXPERIMENT").is_some() {
        return atomic::run(&mut svm, &payer, &args, &protected_keys, instruction,
            &lane, &candidate_afterstate, &request);
    }
'''+needle)
s=s.replace('    let mut svm = LiteSVM::new();', '    let mut svm = LiteSVM::new();\n    if env::var_os("ASPIS_ATOMIC_EXPERIMENT").is_some() {\n        let mut features=LiteSVM::mainnet_feature_set();\n        features.activate(&"txv1aq4pp281K9um3tnPgkfX8UqtFT6wcVW3hNezGLL".parse().unwrap(),0);\n        svm=svm.with_feature_set(features);\n    }')
p.write_text(s)
print('task-owned driver sha256',hashlib.sha256(p.read_bytes()).hexdigest())
