From stlc Require Export fundamental.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import adequacy.
From iris.base_logic Require Export gen_heap.

Definition log_typed `{irisG stlc_lang Σ} (Γ : list type) (e : expr stlc_lang) (τ : type) := ∀ Δ vs,
  env_Persistent Δ →
  ⟦ Γ ⟧* Δ vs ⊢ ⟦ τ ⟧ₑ Δ e.[env_subst vs].
Notation "Γ ⊨ e : τ" := (log_typed Γ e τ) (at level 74, e, τ at next level).

Class stlcPreIG Σ := HeapPreIG {
  stlc_preG_iris :> invPreG Σ;
  stlc_preG_heap :> gen_heapPreG () (val stlc_lang) Σ
}.

Theorem soundness Σ `{stlcPreIG Σ} e τ e' thp σ σ' :
  (∀ `{irisG stlc_lang Σ}, [] ⊨ e : τ) →
  rtc erased_step ([e], σ) (thp, σ') → e' ∈ thp →
  not_stuck e' σ'.
Proof.
  intros Hlog ??.
  cut (adequate NotStuck e σ (λ _ _, True));
    first by intros [_ Hsafe]; eapply Hsafe; eauto.
  eapply (wp_adequacy Σ _). iIntros (Hinv ?).
  destruct H.
  red in σ.
  iMod (gen_heap_init empty) as (Hheap) "[Hh _]".
  iModIntro.
  iExists (λ σ _, gen_heap_interp empty), (λ _, True%I); iFrame.
  (* set (HeapΣ := (irisG stlc_lang Σ)). *)
  iApply (wp_wand with "[]").
  - replace e with e.[env_subst[]] by by asimpl.
    iApply (Hlog _ [] []). iApply (@interp_env_nil _ _).
  - eauto.
Qed.

Corollary type_soundness e τ e' thp σ σ' :
  [] ⊢ₜ e : τ →
  rtc erased_step ([e], σ) (thp, σ') → e' ∈ thp → not_stuck e' σ'.
Proof.
  intros ??.
  set (Σ := #[invΣ ; gen_heapΣ () (val stlc_lang)]).
  set (HG := HeapPreIG Σ _ _).
  eapply (soundness Σ); eauto using fundamental.
  Unshelve. 2 : exact τ. intros.
  eapply fundamental. eauto.
Qed.


