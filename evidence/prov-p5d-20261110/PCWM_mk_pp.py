import re,sys
def block(F,name):
    t=open(F).read()
    m=re.search(r'(?:/--[^\n]*\n(?:    [^\n]*\n)*)?(?:@\[[^\n]*\]\n)?((?:inductive|structure) '+re.escape(name)+r'\b[^\n]*\n(?:[^\n]+\n)*)',t)
    d=re.search(r'(/--(?:[^\n]*\n)(?:    [^\n]*\n)*)(?:@\[[^\n]*\]\n)?(?:inductive|structure) '+re.escape(name)+r'\b',t)
    return (d.group(1) if d else '')+m.group(1)+'\n'
def inject(tag,fresh_blocks):
    f=f'PRVEq_AspisR1PublicPreparation_Types{tag}.lean';t=open(f).read()
    end=f'end PRVFresh_AspisR1PublicPreparation_Types{tag}\n'
    assert end in t
    return f,t.replace(end,fresh_blocks+end,1)
G='AspisR1PublicPreparation'
def names(tag):
    return f'{G}.PRVFresh_AspisR1PublicPreparation_Types{tag}',f'PRVEq.{G}.Types{tag}'
# ---- w1: SemanticPublic and r0.Public (fresh PCVT_E014)
F1='../prov-p1l-20261110/PCVT_E014_emitted/raw/PCVT_stmG/Types.lean'
f,t=inject('_w1',block(F1,'pool_v1.pair_forest_semantic_terminal.SemanticPublic')+block(F1,'pool_v1.pair_forest_semantic_terminal.r0.Public'))
P,E=names('_w1')
S='pool_v1.pair_forest_semantic_terminal'
t+=f'''
def {E}.{S}.SemanticPublic.equiv : {P}.{S}.SemanticPublic ≃ {G}.{S}.SemanticPublic where
  toFun x := {{ variant := {E}.{S}.CompiledVariant.equiv x.variant, pool := x.pool, deployment_domain := x.deployment_domain, anchor := x.anchor, nullifier := x.nullifier, asset_id := x.asset_id, recipient := x.recipient, change := x.change, withdrawal_amount := x.withdrawal_amount, transition := {E}.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1.equiv x.transition }}
  invFun y := {{ variant := ({E}.{S}.CompiledVariant.equiv).symm y.variant, pool := y.pool, deployment_domain := y.deployment_domain, anchor := y.anchor, nullifier := y.nullifier, asset_id := y.asset_id, recipient := y.recipient, change := y.change, withdrawal_amount := y.withdrawal_amount, transition := ({E}.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1.equiv).symm y.transition }}
  left_inv x := by cases x; simp
  right_inv y := by cases y; simp
#print axioms {E}.{S}.SemanticPublic.equiv

def {E}.{S}.r0.Public.equiv : {P}.{S}.r0.Public ≃ {G}.{S}.r0.Public where
  toFun x := match x with
    | .Transfer a b => .Transfer ({E}.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1.equiv a) ({E}.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1.equiv b)
    | .Withdrawal a b => .Withdrawal ({E}.pool_v1.payment_relation.PoolV1WithdrawalPublicV1.equiv a) ({E}.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1.equiv b)
  invFun y := match y with
    | .Transfer a b => .Transfer (({E}.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1.equiv).symm a) (({E}.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1.equiv).symm b)
    | .Withdrawal a b => .Withdrawal (({E}.pool_v1.payment_relation.PoolV1WithdrawalPublicV1.equiv).symm a) (({E}.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1.equiv).symm b)
  left_inv x := by cases x <;> simp
  right_inv y := by cases y <;> simp
#print axioms {E}.{S}.r0.Public.equiv
'''
open(f,'w').write(t)
# ---- w2: TerminalStatementV1 (fresh PCVX_E006)
F2='../prov-p3u-20261110/PCVX_E006_emitted/raw/PCVX_op2124/Types.lean'
f,t=inject('_w2',block(F2,'pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1'))
P,E=names('_w2');S='pool_v1.pair_forest_terminal'
t+=f'''
def {E}.{S}.PoolV1PairForestTerminalStatementV1.equiv : {P}.{S}.PoolV1PairForestTerminalStatementV1 ≃ {G}.{S}.PoolV1PairForestTerminalStatementV1 where
  toFun x := match x with
    | .PrivateTransfer a b => .PrivateTransfer ({E}.{S}.PoolV1PairForestTerminalCommonV1.equiv a) ({E}.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1.equiv b)
    | .Withdrawal a b => .Withdrawal ({E}.{S}.PoolV1PairForestTerminalCommonV1.equiv a) ({E}.pool_v1.payment_relation.PoolV1WithdrawalPublicV1.equiv b)
  invFun y := match y with
    | .PrivateTransfer a b => .PrivateTransfer (({E}.{S}.PoolV1PairForestTerminalCommonV1.equiv).symm a) (({E}.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1.equiv).symm b)
    | .Withdrawal a b => .Withdrawal (({E}.{S}.PoolV1PairForestTerminalCommonV1.equiv).symm a) (({E}.pool_v1.payment_relation.PoolV1WithdrawalPublicV1.equiv).symm b)
  left_inv x := by cases x <;> simp
  right_inv y := by cases y <;> simp
#print axioms {E}.{S}.PoolV1PairForestTerminalStatementV1.equiv
'''
open(f,'w').write(t)
# ---- w3: SemanticTranscript (fresh PCVX_E012)
F3='../prov-p3u-20261110/PCVX_E012_emitted/raw/PCVX_tx2s/Types.lean'
f,t=inject('_w3',block(F3,'r1_wire.SemanticTranscript'))
P,E=names('_w3')
t+=f'''
def {E}.r1_wire.SemanticTranscript.equiv (H : Type) : {P}.r1_wire.SemanticTranscript H ≃ {G}.r1_wire.SemanticTranscript H where
  toFun x := {{ state := x.state, hash := x.hash, next_row := x.next_row }}
  invFun y := {{ state := y.state, hash := y.hash, next_row := y.next_row }}
  left_inv x := by cases x; rfl
  right_inv y := by cases y; rfl
#print axioms {E}.r1_wire.SemanticTranscript.equiv
'''
open(f,'w').write(t)
