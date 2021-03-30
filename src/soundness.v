From iris_examples.logrel.stlc Require Export fundamental.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import adequacy.

Lemma wp_soundness `{irisG stlc_lang Σ} e τ : [] ⊢ₜ e : τ → ⊢ WP e {{ ⟦ τ ⟧ }}.
Proof.
  iIntros (?).
  replace e with e.[env_subst[]] by by asimpl.
  iApply fundamental; eauto. iApply interp_env_nil.
Qed.

Theorem soundness e τ e' thp :
  [] ⊢ₜ e : τ → rtc erased_step ([e], ()) (thp, ()) → e' ∈ thp → not_stuck e' ().
Proof.
  set (Σ := invΣ). intros.
  cut (adequate NotStuck e () (λ _ _, True));
    first by intros [_ Hsafe]; eapply Hsafe; eauto.
  eapply (wp_adequacy Σ _). iIntros (Hinv ?).
  iModIntro. iExists (λ _ _, True%I), (λ _, True%I). iSplit=>//.
  set (HΣ := IrisG _ _ Hinv (λ _ _ _ _, True)%I (λ _, True)%I).
  iApply (wp_wand with "[]"). by iApply wp_soundness. eauto.
Qed.
