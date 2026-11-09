cd "$(dirname "$0")"; P=../prov-p1c-20261109
mk(){ python3 -B PCQE_make_spec.py $P/PCQC_$2_spec.json PCQC_$2 PCQE_$1 $3; }
mk E001 E014   # S004 order
mk E002 E015   # encode_digest_canonical
mk E003 E018   # Dot::push
mk E004 E019   # Weights::raw
mk E005 E020   # S019
mk E006 E016   # S010
mk E007 E025   # expand_values (opacity)
mk E008 E017 roots_s012_a.json
mk E009 E017 roots_s012_b.json
