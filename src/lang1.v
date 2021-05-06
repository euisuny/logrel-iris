From iris.program_logic Require Export language ectx_language ectxi_language.
From cbpv Require Import base syntax semantics.

(* | pstepForce (c: comp n): *)
(*     <{c}>! ≽ c *)
(* | pstepApp (c: comp (S n)) (c': comp n) v: *)
(*     c[v..] = c' -> (lambda c) v ≽ c' *)
(* | pstepProj (b: bool) (c c1 c2: comp n) : *)
(*     (c = if b then c1 else c2) -> proj b (tuple c1 c2) ≽ c *)
(* | pstepLetin (c: comp (S n)) c' v: *)
(*     c[v..] = c' -> $ <- (ret v); c ≽ c' *)
(* | pstepCaseS v (b: bool) c (c1 c2: comp (S n)): *)
(*     (if b then c1 else c2)[v..] = c -> caseS (inj b v) c1 c2 ≽ c *)
(* | pstepCaseP v1 v2 (c: comp (S (S n))) c': *)
(*     c[v2,v1..] = c' -> caseP (pair v1 v2) c ≽ c' *)
Inductive val :=
  | UnitV
  (* | ThunkV (v : val) *)
  (* | LambdaV (v : val) *) (* Step value is weird*)
  | TupleV (v1 v2 : val).
(* what to do with the values? *)
  (* | RetV (v : val) *)
  (* | InjV (b : bool) (v : val) *)
  (* | PairV (v1 v2 : val). *)

Fixpoint of_val {n : nat} (v : val) : comp n :=
  match v with
  | UnitV => cu
  (* | ThunkV () => of_val v *)
  (* | LambdaV v => lambda (of_val v) *)
  | TupleV v1 v2 => tuple (of_val v1) (of_val v2)
  (* | RetV v => ret (thunk (of_val v)) *)
  (* | InjV b v => inj b (of_val v) *)
  (* | PairV v1 v2 => tuple (of_val v1) (of_val v2) *)
  (* | InjLV v1 => proj true (of_val v1) *)
  (* | InjRV v1 => proj false (of_val v1) *)
  end.

Fixpoint to_val {n : nat} (c : comp n) : option val :=
  match c with
  | cu => Some UnitV
  (* | lambda e => v ← to_val e ; Some (LambdaV v) *)
  | tuple e1 e2 => v1 ← to_val e1 ; v2 ← to_val e2 ; Some (TupleV v1 v2)
  (* | proj true e1 => v1 ← to_val e1 ; Some (InjLV v1) *)
  (* | proj false e1 => v1 ← to_val e1 ; Some (InjRV v1) *)
  | _ => None
  end.

Variant head_step {n : nat} : comp n -> unit -> list unit -> comp n -> unit -> list (comp n) -> Prop :=
| strong_head_step c1 c2 : strong_step c1 c2 ->
                     head_step c1 tt nil c2 tt nil.

Lemma fillc_item_inj n m:
  ∀ Ki : cctx false n m, Inj eq eq (@fillc n _ _ Ki).
Proof.
  revert n m.
  eapply mutind_vctx_cctx ; cbn; exintuition.
  all : repeat intro; intuition ; try contradiction.
  all : match goal with
  | [ IH: Inj _ _ _ , H : _ = _ |- _] => eapply IH; inv H; eauto
  end.
Qed.

Lemma fillv_item_inj n m:
  ∀ Ki : vctx false n m, Inj eq eq (@fillv n _ _ Ki).
Proof.
  intro.
  eapply mutind_vctx_cctx with (m := n) (n := m) (t := false)
                               (v := Ki).
  all : cbn; exintuition.
  all : repeat intro; intuition; inv H0; try apply H; auto with f_equal.
Qed.

(** Basic properties about the language *)
Lemma to_of_val n v : @to_val n (@of_val n v) = Some v.
Proof. revert n. induction v; intros; try simplify_option_eq. all : try eauto.
Qed.

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
  intros Ki e [v ?].
  revert e v H.
  dependent induction Ki; intros; simplify_option_eq; eauto.
Qed.

Lemma val_head_stuck n e1 σ1 κ e2 σ2 efs : head_step e1 σ1 κ e2 σ2 efs → @to_val n e1 = None.
Proof.
  destruct 1.
  destruct H.
  revert K.
  induction H; try naive_solver; dependent induction K; try simplify_option_eq; auto.
  all : destruct (to_val c0); auto; repeat simplify_option_eq; auto.
Qed.

Lemma head_ctx_step_val n
      (Ki : cctx false n n) (e : comp n) (σ1 : ()) (κ : list ()) (e2 : comp n) (σ2 : ()) (efs : list (comp n)):
    head_step (fillc Ki e) σ1 κ e2 σ2 efs → is_Some (to_val e).
Proof.
  revert e σ1 e2 σ2 efs.
  dependent induction Ki.
  - (* cctxForce *)
    cbn. inversion_clear 1. inv H0. inv H1.
    (* + induction K. inv H. pose proof fillv_item_inj. *)
    (*   red in H. specialize (H _ _ _ _ _ H1).  *)
    (* simplify_option_eq.  *)
Admitted.

Lemma fill_item_no_val_inj n:
 ∀ (Ki1 Ki2 : cctx false n n) (e1 e2 : comp n),
   @to_val n e1 = None → @to_val n e2 = None → fillc Ki1 e1 = fillc Ki2 e2 → Ki1 = Ki2.
Proof.
  (* intros Ki1 Ki2;  dependent destruction Ki1; dependent destruction Ki2; intros; try discriminate; simplify_eq; *)
  (* repeat match goal with *)
  (*         | H : to_val (of_val _) = None |- _ => by rewrite to_of_val in H *)
  (*        end; auto. *)
  (* cbn. subst. eauto. cbn. unfold cctxHole. red. apply fill_item_inj in H1. inv H1. *)
  (* Qed. *)
Admitted.

Lemma lang_mixin n : EctxiLanguageMixin (@of_val n) (@to_val n) (fillc (t := false)) head_step.
Proof.
  split; auto.
  - eapply (to_of_val n).
  - eapply (of_to_val n).
  - apply val_head_stuck.
  - apply fill_item_val.
  - eapply fillc_item_inj.
  - admit.
    (* apply fill_item_no_val_inj. *)
  - apply head_ctx_step_val.
Admitted.
