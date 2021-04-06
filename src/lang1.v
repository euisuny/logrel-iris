From iris.program_logic Require Export language ectx_language ectxi_language.
From cbpv Require Import base syntax semantics.

Definition of_val (n : nat) (v : value n) : comp n := ret v.

Definition to_val (n : nat) (c : comp n) : option (value n) :=
  match c with
  | ret v => Some v
  | _ => None
  end.

Variant head_step {n : nat} : comp n -> unit -> list unit -> comp n -> unit -> list (comp n) -> Prop :=
| cstep_step c1 c2 : cstep c1 c2 ->
                     head_step c1 tt nil c2 tt nil.


Lemma Inj_fill n:
  ∀ Ki : ectx, Inj eq eq (@fill n Ki).
Proof.
  intros. induction Ki; repeat intro; auto; inv H; apply IHKi; auto.
Qed.

Lemma to_of_val n v : to_val n (of_val n v) = Some v.
  Proof. by induction v; simplify_option_eq. Qed.


Lemma lang_mixin n : EctxiLanguageMixin (of_val n) (to_val n) fill head_step.
Proof.
  split; auto.
  - unfold of_val, to_val. intros. destruct e; inversion H; auto.
  - intros. inversion H. subst. inversion H0. subst. inv H1; destruct C; simpl; auto.
  - intros. destruct Ki; simpl in *; auto; try inv H; inv H0.
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
