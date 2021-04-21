From stlc Require Export logrel.
From iris.proofmode Require Import tactics.
From stlc Require Import rules.
From iris.program_logic Require Import lifting.

From iris.base_logic Require Import invariants.
From iris.proofmode Require Import tactics.

Section typed_interp.

Definition log_typed `{irisG stlc_lang Σ} (Γ : list type) (e : expr stlc_lang) (τ : type) := ∀ Δ vs,
  env_Persistent Δ →
  ⟦ Γ ⟧* Δ vs ⊢ ⟦ τ ⟧ₑ Δ e.[env_subst vs].
Notation "Γ ⊨ e : τ" := (log_typed Γ e τ) (at level 74, e, τ at next level).

Context `{LANG: irisG stlc_lang Σ}.
  Notation D := (valO stlc_lang -n> iPropO Σ).
  Local Tactic Notation "smart_wp_bind" uconstr(ctx) ident(v) constr(Hv) uconstr(Hp) :=
    iApply (wp_bind (fill [ctx]));
    iApply (wp_wand with "[-]"); [iApply Hp; trivial|]; cbn;
    iIntros (v) Hv.

  Theorem fundamental Γ e τ : Γ ⊢ₜ e : τ → Γ ⊨ e : τ.
  Proof.
    induction 1; iIntros (Δ vs HΔ) "#HΓ /=".
    - (* var *)
      iDestruct (interp_env_Some_l with "HΓ") as (v) "[% ?]"; first done.
      erewrite env_subst_lookup; eauto.
        by iApply wp_value.
    - (* unit *) iApply wp_value; trivial.
    - (* pair *)
      smart_wp_bind (PairLCtx e2.[env_subst vs]) v "#Hv" IHtyped1.
      smart_wp_bind (PairRCtx v) v' "# Hv'" IHtyped2.
      iApply wp_value; eauto.
    - (* fst *)
      smart_wp_bind (FstCtx) v "# Hv" IHtyped; cbn.
      iDestruct "Hv" as (w1 w2) "#[% [H2 H3]]"; subst.
      iApply wp_pure_step_later; auto. by iApply wp_value.
    - (* snd *)
      smart_wp_bind (SndCtx) v "# Hv" IHtyped; cbn.
      iDestruct "Hv" as (w1 w2) "#[% [H2 H3]]"; subst.
      iApply wp_pure_step_later; auto. by iApply wp_value.
    - (* injl *)
      smart_wp_bind (InjLCtx) v "# Hv" IHtyped; cbn.
      iApply wp_value; eauto.
    - (* injr *)
      smart_wp_bind (InjRCtx) v "# Hv" IHtyped; cbn.
      iApply wp_value; eauto.
    - (* case *)
      smart_wp_bind (CaseCtx _ _) v "#Hv" IHtyped1; cbn.
      iDestruct (interp_env_length with "HΓ") as %?.
      iDestruct "Hv" as "[Hv|Hv]"; iDestruct "Hv" as (w) "[% Hw]"; simplify_eq/=.
      + iApply wp_pure_step_later; auto 1 using to_of_val; asimpl. iNext.
        iApply (IHtyped2 Δ (w :: vs)). iApply interp_env_cons; auto.
      + iApply wp_pure_step_later; auto 1 using to_of_val; asimpl. iNext.
        iApply (IHtyped3 Δ (w :: vs)). iApply interp_env_cons; auto.
    - (* Lam *)
      iApply wp_value. simpl. iModIntro. iIntros (w) "#Hw".
      iDestruct (interp_env_length with "HΓ") as %?.
      iApply wp_pure_step_later; auto 1 using to_of_val. iNext.
      asimpl.
      iApply (IHtyped Δ (w :: vs)); auto.
      iApply interp_env_cons; iSplit; auto.
    - (* app *)
      smart_wp_bind (AppLCtx (e2.[env_subst vs])) v "#Hv" IHtyped1.
      smart_wp_bind (AppRCtx v) w "#Hw" IHtyped2.
      by iApply "Hv".
    - (* Rec *)
      iApply wp_value. simpl. iModIntro. iLöb as "IH". iIntros (w) "#Hw".
      iDestruct (interp_env_length with "HΓ") as %?.
      iApply wp_pure_step_later; auto 1 using to_of_val.
      iNext.
      asimpl. change (Rec _) with (of_val (RecV e.[upn 2 (env_subst vs)])) at 2.
      iApply (IHtyped Δ (_ :: w :: vs)).
      iApply interp_env_cons; iSplit; [|iApply interp_env_cons]; auto.
    - (* Fold *)
      iApply (wp_bind (fill [FoldCtx]));
        iApply wp_wand_l; iSplitL; [|iApply (IHtyped Δ vs); auto].
      iIntros (v) "#Hv". iApply wp_value.
      rewrite /= -interp_subst fixpoint_interp_rec1_eq /=.
      iModIntro; eauto.
    - (* Unfold *)
      iApply (wp_bind (fill [UnfoldCtx]));
        iApply wp_wand_l; iSplitL; [|iApply IHtyped; auto].
      iIntros (v) "#Hv". rewrite /= fixpoint_interp_rec1_eq.
      change (fixpoint _) with (⟦ TRec τ ⟧ Δ); simpl.
      iDestruct "Hv" as (w) "#[% Hw]"; subst.
      iApply wp_pure_step_later; cbn; auto using to_of_val.
      iNext. iApply wp_value. by iApply interp_subst.
  Qed.

End typed_interp.
