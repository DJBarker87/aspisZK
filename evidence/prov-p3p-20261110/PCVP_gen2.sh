#!/bin/bash
# generates PRVEq_AdapterStage{1,2}DeployedNOC_o1.lean from the P3o deployed files + NOC corrected-seed section
cd "$(dirname "$0")"
for k in 1 2; do
S=../prov-p3o-20261110/PRVEq_AdapterStage${k}Deployed_o1.lean
O=PRVEq_AdapterStage${k}DeployedNOC_o1.lean
n=$(grep -n '^#print axioms bound' $S | cut -d: -f1)
head -$((n-1)) $S | sed -e "s/namespace PCVO_S$k/namespace PCVP_S$k/" -e 's/^import NNH_Tx2SourceConfiguration/import NNH_Tx2SourceConfiguration\nimport NOC_Run5bHost/' > $O
if [ $k = 1 ]; then
cat >> $O <<'EOT'

/-- Corrected seed: the headline's model1 (NOC_HostCtx.model1 c = stage1_owned (NOC_HostCtx.sdk c)); seed-generic by rfl. -/
theorem noc_model1 {W Tx : Type} (c : AspisR1.NNH_HostCtx.Ctx W Tx) :
    AdapterRw.PCVK_S1.r1_pool_adapter.owned.stage1_owned (xOf (AspisR1.NOC_HostCtx.sdk c)) = AspisR1.NOC_HostCtx.model1 c :=
  generic_stage1_owned _
#print axioms noc_model1
end PCVP_S1
EOT
else
cat >> $O <<'EOT'

/-- Corrected seed: NOC_HostCtx.model2 c = stage2_owned (NOC_HostCtx.sdk c); hashv instantiated as LIB_Env.hashv (envOf c)
(deployed op43 is `fun _ parts => hashv parts` by rfl). NOC_HostCtx.hashv c (= DGP_HostDigest.hashvInst c.sha256) is
not identified with LIB_Env.hashv here; that identification is DGP_HostDigest's, not claimed. -/
theorem noc_model2 {W Tx : Type} (c : AspisR1.NNH_HostCtx.Ctx W Tx) :
    AdapterRw.PCVK_S2.r1_pool_adapter.owned.stage2_owned (xOf (AspisR1.NOC_HostCtx.sdk c) (LIB_Env.hashv (AspisR1.NOC_HostCtx.envOf c))) =
      AspisR1.NOC_HostCtx.model2 c :=
  generic_stage2_owned _ _ rfl rfl
#print axioms noc_model2
end PCVP_S2
EOT
fi
done
