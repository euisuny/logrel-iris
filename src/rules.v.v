From iris.program_logic Require Export weakestpre.
From iris.proofmode Require Export tactics.
From iris.program_logic Require Import ectx_lifting.
From cbpv Require Export lang.
From stdpp Require Import fin_maps.

Section stlc_rules.
  Context `{irisG stlc_lang Σ}.
  Implicit Types e : expr.

  Ltac inv_head_step :=
    repeat match goal with
    | H : to_val _ = Some _ |- _ => apply of_to_val in H
    | H : head_step ?e _ _ _ _ _ |- _ =>
       try (is_var e; fail 1); (* inversion yields many goals if [e] is a variable
       and can thus better be avoided. *)
       inversion H; subst; clear H
    end.

  Local Hint Extern 0 (head_reducible _ _) => eexists _, _, _, _; simpl : core.

  Local Hint Constructors head_step : core.
  Local Hint Resolve to_of_val : core.

  Local Ltac solve_exec_safe := intros; subst; do 3 eexists; econstructor; eauto.
  Local Ltac solve_exec_puredet := simpl; intros; by inv_head_step.
  Local Ltac solve_pure_exec :=
    unfold IntoVal in *;
    repeat match goal with H : AsVal _ |- _ => destruct H as [??] end; subst;
    intros ?; apply nsteps_once, pure_head_step_pure_step;
      constructor; [solve_exec_safe | solve_exec_puredet].

  (** Helper Lemmas for weakestpre. *)

  Global Instance pure_lam e1 e2 `{!AsVal e2}:
    PureExec True 1 (App (Lam e1) e2) (e1.[e2 /]).
  Proof. solve_pure_exec. Qed.

  Global Instance pure_fst e1 e2 `{!AsVal e1, !AsVal e2}:
    PureExec True 1 (Fst (Pair e1 e2)) e1.
  Proof. solve_pure_exec. Qed.

  Global Instance pure_snd e1 e2 `{!AsVal e1, !AsVal e2}:
    PureExec True 1 (Snd (Pair e1 e2)) e2.
  Proof. solve_pure_exec. Qed.

  Global Instance pure_case_inl e0 e1 e2 `{!AsVal e0}:
    PureExec True 1 (Case (InjL e0) e1 e2) e1.[e0/].
  Proof. solve_pure_exec. Qed.

  Global Instance pure_case_inr e0 e1 e2 `{!AsVal e0}:
    PureExec True 1 (Case (InjR e0) e1 e2) e2.[e0/].
  Proof. solve_pure_exec. Qed.

End stlc_rules.
