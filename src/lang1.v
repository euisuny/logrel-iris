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

Lemma lang_mixin n : EctxiLanguageMixin (of_val n) (to_val n) fill head_step.
Proof.
  split; auto.
  - unfold of_val, to_val. intros. destruct e; inversion H; auto.
  - intros. inversion H. subst. inversion H0. subst. inv H1; destruct C; simpl; auto.
  - intros. destruct Ki; simpl in *; auto; try inv H; inv H0.
  - intros. induction Ki; repeat intro; auto; inv H; apply IHKi; auto.
  - intros.
    destruct Ki1, Ki2; inv H1; auto. simpl in H2.
    inv H2.
  split; apply _ || eauto using to_of_val, of_to_val, val_head_stuck,
         fill_item_.,`val, fill_item_no_val_inj, head_ctx_step_val.
Qed.
