From iris.program_logic Require Export language ectx_language ectxi_language.
From cbpv Require Import base syntax semantics.
Definition of_val (n : nat) (v : value n) : comp n := ret v.

Definition to_val (n : nat) (c : comp n) : option (value n) :=
  match c with
  | ret v => Some v
  | _ => None
  end.

Variant head_step {n : nat} : comp n -> unit -> list unit -> comp n -> unit -> list (comp n) -> Prop :=
| strong_head_step c1 c2 : strong_step c1 c2 ->
                     head_step c1 tt nil c2 tt nil.

Lemma Inj_fill_vctx n m:
  ∀ Ki : cctx false n m, Inj eq eq (@fillc n _ _ Ki).
Proof.
  revert n m.
  eapply mutind_vctx_cctx; cbn; exintuition.
  all : repeat intro; intuition ; try contradiction.
  all : match goal with
  | [ IH: Inj _ _ _ , H : _ = _ |- _] => eapply IH; inv H; eauto
  end.
Qed.

Lemma to_of_val n v : to_val n (of_val n v) = Some v.
Proof. by induction v; try simplify_option_eq. Qed.

Require Import Coq.Program.Equality.
Lemma lang_mixin n : EctxiLanguageMixin (of_val n) (to_val n) (fillc (t := false)) head_step.
Proof.
  split; auto.
  - unfold of_val, to_val. intros. destruct e; inversion H; auto.
  - intros. inv H. inv H0.
    (* revert n m c1 K c2 H. eapply mutind_vctx_cctx; cbn; intuition. *)
    (* all : repeat intro; intuiition; *)
    (* destruct K; eauto. clear H. destruct y. *)
    (* cbn.  *)
  (* destruct K; simpl; eauto. inv y. eauto. inv H; destruct K; simpl; auto.  exintuition. *)
    admit.
  - revert n.
    (* eapply mutind_vctx_cctx; cbn; exintuition. *)
    (* Unshelve. 5 : exact false. *)
    admit.
    (* eauto.  *)

    (* dependent induction Ki. *)
    (* 1-3: intros; eauto.  cbn in H; try solve [inv H; inv H0]. *)
    (* revert e H. *)
    (* dependent induction v. inv y. *)
    (* all : intros; try eapply IHv; eauto. *)

    (* eapply  *)

  (* inv H. inv H0.  *)



  - apply Inj_fill.
  - induction Ki1, Ki2; intros; try discriminate; simplify_eq;
    repeat match goal with
           | H : to_val (of_val _) = None |- _ => by rewrite to_of_val in H
           end; auto.

    eapply IHKi1 in H1; subst; eauto.
    eapply IHKi1 in H2; subst; eauto.
    eapply IHKi1 in H1; subst; eauto.
  - destruct Ki; inversion_clear 1; simplify_option_eq; eauto.
    inv H0. 
    inv H0. 
  split; apply _ || eauto using to_of_val, of_to_val, val_head_stuck,
         fill_item_.,`val, fill_item_no_val_inj, head_ctx_step_val.
Qed.

EctxiLanguageMixin
