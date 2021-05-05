From iris.program_logic Require Export language ectx_language ectxi_language.
From cbpv Require Import base syntax semantics.

Inductive val :=
  | PairV (v1 v2 : val)
  | UnitV
  | InjLV (v : val)
  | InjRV (v : val).

Fixpoint of_val {n : nat} (v : val) : comp n :=
  match v with
  | PairV v1 v2 => tuple (of_val v1) (of_val v2)
  | UnitV => cu
  | InjLV v1 => proj true (of_val v1)
  | InjRV v1 => proj false (of_val v1)
  end.

Fixpoint to_val {n : nat} (c : comp n) : option val :=
  match c with
  | cu => Some UnitV
  | tuple e1 e2 => v1 ← to_val e1 ; v2 ← to_val e2 ; Some (PairV v1 v2)
  | proj true e1 => v1 ← to_val e1 ; Some (InjLV v1)
  | proj false e1 => v1 ← to_val e1 ; Some (InjRV v1)
  | _ => None
  end.

Variant head_step {n : nat} : comp n -> unit -> list unit -> comp n -> unit -> list (comp n) -> Prop :=
| strong_head_step c1 c2 : strong_step c1 c2 ->
                     head_step c1 tt nil c2 tt nil.

Lemma fill_item_inj n m:
  ∀ Ki : cctx false n m, Inj eq eq (@fillc n _ _ Ki).
Proof.
  revert n m.
  eapply mutind_vctx_cctx; cbn; exintuition.
  all : repeat intro; intuition ; try contradiction.
  all : match goal with
  | [ IH: Inj _ _ _ , H : _ = _ |- _] => eapply IH; inv H; eauto
  end.
Qed.

(** Basic properties about the language *)
Lemma to_of_val n v : @to_val n (@of_val n v) = Some v.
Proof. induction v; try simplify_option_eq. all : try eauto. Qed.

Lemma of_to_val:
  ∀ n (e : comp n) (v : val), @to_val n e = Some v → @of_val n v = e.
Proof.
  intros n e; induction e; try destruct b; intros; simplify_option_eq; auto with f_equal.
Qed.

Instance of_val_inj n : Inj (=) (=) (@of_val n).
Proof.
  intros ?? Hv; apply (stdpp.base.inj Some); rewrite -!(to_of_val n) Hv. auto. Qed.

Require Import Coq.Program.Equality.
Lemma fill_item_val n:
 ∀ (Ki : cctx false n n) (e : comp n), is_Some (@to_val n (fillc Ki e)) → is_Some (@to_val n e).
Proof.
  intros Ki e [v ?]. dependent induction Ki; simplify_option_eq; eauto.
  destruct b; simplify_option_eq; eapply IHKi; eauto.
Qed.

Lemma head_ctx_step_val n
      (Ki : cctx false n n) (e : comp n) (σ1 : ()) (κ : list ()) (e2 : comp n) (σ2 : ()) (efs : list (comp n)):
    head_step (fillc Ki e) σ1 κ e2 σ2 efs → is_Some (to_val e).
Proof.
  dependent induction Ki.
  (* cctxHole *)
  - inversion_clear 1; simplify_option_eq; eauto.
    inv H0.
Admitted.

(* Qed. *)
(*   destruct Ki; inversion_clear 1; simplify_option_eq; eauto. *)
(*   inv y. *)
(* Admitted. *)

(* Lemma fill_item_no_val_inj n: *)
(*  ∀ (Ki1 Ki2 : cctx false n n) (e1 e2 : comp n), *)
(*    @to_val n e1 = None → @to_val n e2 = None → fillc Ki1 e1 = fillc Ki2 e2 → Ki1 = Ki2. *)
(* Proof. *)
(*   (* intros Ki1 Ki2;  dependent destruction Ki1; dependent destruction Ki2; intros; try discriminate; simplify_eq; *) *)
(*   (* repeat match goal with *) *)
(*   (*         | H : to_val (of_val _) = None |- _ => by rewrite to_of_val in H *) *)
(*   (*        end; auto. *) *)
(*   (* cbn. subst. eauto. cbn. unfold cctxHole. red. apply fill_item_inj in H1. inv H1. *) *)
(*   (* Qed. *) *)
(* Admitted. *)

Lemma val_head_stuck n e1 σ1 κ e2 σ2 efs : head_step e1 σ1 κ e2 σ2 efs → @to_val n e1 = None.
Proof. Admitted.

Lemma lang_mixin n : EctxiLanguageMixin (@of_val n) (@to_val n) (fillc (t := false)) head_step.
Proof.
  split; auto.
  - eapply (to_of_val n).
  - eapply (of_to_val n).
  - apply val_head_stuck.
  - apply fill_item_val.
  - eapply fill_item_inj.
  - admit.
    (* apply fill_item_no_val_inj. *)
  - apply head_ctx_step_val.
Admitted.
