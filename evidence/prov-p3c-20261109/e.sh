# show errors and PRVC axioms only
xz -dc /Users/dominic/ZK/.worktrees/pc-prov-p3c/evidence/prov-p3c-20261109/$1/stdout.log.xz | awk '/error/{p=1} /warning/{p=0} /^\x27PRV/{print; p=0} p{print}' | head -${2:-80}
