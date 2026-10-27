Require S.Lib.
Definition local := (S.Lib.top3, S.Lib.top1).
Section L.
  Variable v : nat.
  Definition uses_v := v + S.Base.base_def + S.Lib.top2.
  Print Assumptions uses_v.
End L.
Print Assumptions local.
Print Assumptions S.Lib.FM.fl.
Print Assumptions S.Base.tree.
