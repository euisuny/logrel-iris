From cbpv Require Export fintype.
From cbpv Require Export header_extensible.

Section valtypecomptype.
Inductive valtype  : Type :=
  | zero : valtype
  | one : valtype
  | U : comptype   -> valtype
  | Sigma : valtype   -> valtype   -> valtype
  | cross : valtype   -> valtype   -> valtype
 with comptype  : Type :=
  | cone : comptype
  | F : valtype   -> comptype
  | Pi : comptype   -> comptype   -> comptype
  | arrow : valtype   -> comptype   -> comptype .

Lemma congr_zero  : zero  = zero  .
Proof. congruence. Qed.

Lemma congr_one  : one  = one  .
Proof. congruence. Qed.

Lemma congr_U  { s0 : comptype   } { t0 : comptype   } (H1 : s0 = t0) : U s0 = U t0 .
Proof. congruence. Qed.

Lemma congr_Sigma  { s0 : valtype   } { s1 : valtype   } { t0 : valtype   } { t1 : valtype   } (H1 : s0 = t0) (H2 : s1 = t1) : Sigma s0 s1 = Sigma t0 t1 .
Proof. congruence. Qed.

Lemma congr_cross  { s0 : valtype   } { s1 : valtype   } { t0 : valtype   } { t1 : valtype   } (H1 : s0 = t0) (H2 : s1 = t1) : cross s0 s1 = cross t0 t1 .
Proof. congruence. Qed.

Lemma congr_cone  : cone  = cone  .
Proof. congruence. Qed.

Lemma congr_F  { s0 : valtype   } { t0 : valtype   } (H1 : s0 = t0) : F s0 = F t0 .
Proof. congruence. Qed.

Lemma congr_Pi  { s0 : comptype   } { s1 : comptype   } { t0 : comptype   } { t1 : comptype   } (H1 : s0 = t0) (H2 : s1 = t1) : Pi s0 s1 = Pi t0 t1 .
Proof. congruence. Qed.

Lemma congr_arrow  { s0 : valtype   } { s1 : comptype   } { t0 : valtype   } { t1 : comptype   } (H1 : s0 = t0) (H2 : s1 = t1) : arrow s0 s1 = arrow t0 t1 .
Proof. congruence. Qed.

End valtypecomptype.

Section valuecomp.
Inductive value (nvalue : nat) : Type :=
  | var_value : (fin) (nvalue) -> value (nvalue)
  | u : value (nvalue)
  | pair : value  (nvalue) -> value  (nvalue) -> value (nvalue)
  | inj : bool   -> value  (nvalue) -> value (nvalue)
  | thunk : comp  (nvalue) -> value (nvalue)
 with comp (nvalue : nat) : Type :=
  | cu : comp (nvalue)
  | force : value  (nvalue) -> comp (nvalue)
  | lambda : comp  ((S) nvalue) -> comp (nvalue)
  | app : comp  (nvalue) -> value  (nvalue) -> comp (nvalue)
  | tuple : comp  (nvalue) -> comp  (nvalue) -> comp (nvalue)
  | ret : value  (nvalue) -> comp (nvalue)
  | letin : comp  (nvalue) -> comp  ((S) nvalue) -> comp (nvalue)
  | proj : bool   -> comp  (nvalue) -> comp (nvalue)
  | caseZ : value  (nvalue) -> comp (nvalue)
  | caseS : value  (nvalue) -> comp  ((S) nvalue) -> comp  ((S) nvalue) -> comp (nvalue)
  | caseP : value  (nvalue) -> comp  ((S) ((S) nvalue)) -> comp (nvalue).

Lemma congr_u { mvalue : nat } : u (mvalue) = u (mvalue) .
Proof. congruence. Qed.

Lemma congr_pair { mvalue : nat } { s0 : value  (mvalue) } { s1 : value  (mvalue) } { t0 : value  (mvalue) } { t1 : value  (mvalue) } (H1 : s0 = t0) (H2 : s1 = t1) : pair (mvalue) s0 s1 = pair (mvalue) t0 t1 .
Proof. congruence. Qed.

Lemma congr_inj { mvalue : nat } { s0 : bool   } { s1 : value  (mvalue) } { t0 : bool   } { t1 : value  (mvalue) } (H1 : s0 = t0) (H2 : s1 = t1) : inj (mvalue) s0 s1 = inj (mvalue) t0 t1 .
Proof. congruence. Qed.

Lemma congr_thunk { mvalue : nat } { s0 : comp  (mvalue) } { t0 : comp  (mvalue) } (H1 : s0 = t0) : thunk (mvalue) s0 = thunk (mvalue) t0 .
Proof. congruence. Qed.

Lemma congr_cu { mvalue : nat } : cu (mvalue) = cu (mvalue) .
Proof. congruence. Qed.

Lemma congr_force { mvalue : nat } { s0 : value  (mvalue) } { t0 : value  (mvalue) } (H1 : s0 = t0) : force (mvalue) s0 = force (mvalue) t0 .
Proof. congruence. Qed.

Lemma congr_lambda { mvalue : nat } { s0 : comp  ((S) mvalue) } { t0 : comp  ((S) mvalue) } (H1 : s0 = t0) : lambda (mvalue) s0 = lambda (mvalue) t0 .
Proof. congruence. Qed.

Lemma congr_app { mvalue : nat } { s0 : comp  (mvalue) } { s1 : value  (mvalue) } { t0 : comp  (mvalue) } { t1 : value  (mvalue) } (H1 : s0 = t0) (H2 : s1 = t1) : app (mvalue) s0 s1 = app (mvalue) t0 t1 .
Proof. congruence. Qed.

Lemma congr_tuple { mvalue : nat } { s0 : comp  (mvalue) } { s1 : comp  (mvalue) } { t0 : comp  (mvalue) } { t1 : comp  (mvalue) } (H1 : s0 = t0) (H2 : s1 = t1) : tuple (mvalue) s0 s1 = tuple (mvalue) t0 t1 .
Proof. congruence. Qed.

Lemma congr_ret { mvalue : nat } { s0 : value  (mvalue) } { t0 : value  (mvalue) } (H1 : s0 = t0) : ret (mvalue) s0 = ret (mvalue) t0 .
Proof. congruence. Qed.

Lemma congr_letin { mvalue : nat } { s0 : comp  (mvalue) } { s1 : comp  ((S) mvalue) } { t0 : comp  (mvalue) } { t1 : comp  ((S) mvalue) } (H1 : s0 = t0) (H2 : s1 = t1) : letin (mvalue) s0 s1 = letin (mvalue) t0 t1 .
Proof. congruence. Qed.

Lemma congr_proj { mvalue : nat } { s0 : bool   } { s1 : comp  (mvalue) } { t0 : bool   } { t1 : comp  (mvalue) } (H1 : s0 = t0) (H2 : s1 = t1) : proj (mvalue) s0 s1 = proj (mvalue) t0 t1 .
Proof. congruence. Qed.

Lemma congr_caseZ { mvalue : nat } { s0 : value  (mvalue) } { t0 : value  (mvalue) } (H1 : s0 = t0) : caseZ (mvalue) s0 = caseZ (mvalue) t0 .
Proof. congruence. Qed.

Lemma congr_caseS { mvalue : nat } { s0 : value  (mvalue) } { s1 : comp  ((S) mvalue) } { s2 : comp  ((S) mvalue) } { t0 : value  (mvalue) } { t1 : comp  ((S) mvalue) } { t2 : comp  ((S) mvalue) } (H1 : s0 = t0) (H2 : s1 = t1) (H3 : s2 = t2) : caseS (mvalue) s0 s1 s2 = caseS (mvalue) t0 t1 t2 .
Proof. congruence. Qed.

Lemma congr_caseP { mvalue : nat } { s0 : value  (mvalue) } { s1 : comp  ((S) ((S) mvalue)) } { t0 : value  (mvalue) } { t1 : comp  ((S) ((S) mvalue)) } (H1 : s0 = t0) (H2 : s1 = t1) : caseP (mvalue) s0 s1 = caseP (mvalue) t0 t1 .
Proof. congruence. Qed.

Definition upRen_value_value { m : nat } { n : nat } (xi : (fin) (m) -> (fin) (n)) : (fin) ((S) (m)) -> (fin) ((S) (n)) :=
  (up_ren) xi.

Definition upRenList_value_value (p : nat) { m : nat } { n : nat } (xi : (fin) (m) -> (fin) (n)) : (fin) (p+ (m)) -> (fin) (p+ (n)) :=
  upRen_p p xi.

Fixpoint ren_value { mvalue : nat } { nvalue : nat } (xivalue : (fin) (mvalue) -> (fin) (nvalue)) (s : value (mvalue)) : value (nvalue) :=
    match s with
    | var_value (_) s => (var_value (nvalue)) (xivalue s)
    | u (_)  => u (nvalue)
    | pair (_) s0 s1 => pair (nvalue) ((ren_value xivalue) s0) ((ren_value xivalue) s1)
    | inj (_) s0 s1 => inj (nvalue) ((fun x => x) s0) ((ren_value xivalue) s1)
    | thunk (_) s0 => thunk (nvalue) ((ren_comp xivalue) s0)
    end
 with ren_comp { mvalue : nat } { nvalue : nat } (xivalue : (fin) (mvalue) -> (fin) (nvalue)) (s : comp (mvalue)) : comp (nvalue) :=
    match s with
    | cu (_)  => cu (nvalue)
    | force (_) s0 => force (nvalue) ((ren_value xivalue) s0)
    | lambda (_) s0 => lambda (nvalue) ((ren_comp (upRen_value_value xivalue)) s0)
    | app (_) s0 s1 => app (nvalue) ((ren_comp xivalue) s0) ((ren_value xivalue) s1)
    | tuple (_) s0 s1 => tuple (nvalue) ((ren_comp xivalue) s0) ((ren_comp xivalue) s1)
    | ret (_) s0 => ret (nvalue) ((ren_value xivalue) s0)
    | letin (_) s0 s1 => letin (nvalue) ((ren_comp xivalue) s0) ((ren_comp (upRen_value_value xivalue)) s1)
    | proj (_) s0 s1 => proj (nvalue) ((fun x => x) s0) ((ren_comp xivalue) s1)
    | caseZ (_) s0 => caseZ (nvalue) ((ren_value xivalue) s0)
    | caseS (_) s0 s1 s2 => caseS (nvalue) ((ren_value xivalue) s0) ((ren_comp (upRen_value_value xivalue)) s1) ((ren_comp (upRen_value_value xivalue)) s2)
    | caseP (_) s0 s1 => caseP (nvalue) ((ren_value xivalue) s0) ((ren_comp (upRen_value_value (upRen_value_value xivalue))) s1)
    end.

Definition up_value_value { m : nat } { nvalue : nat } (sigma : (fin) (m) -> value (nvalue)) : (fin) ((S) (m)) -> value ((S) nvalue) :=
  (scons) ((var_value ((S) nvalue)) (var_zero)) ((funcomp) (ren_value (shift)) sigma).

Definition upList_value_value (p : nat) { m : nat } { nvalue : nat } (sigma : (fin) (m) -> value (nvalue)) : (fin) (p+ (m)) -> value (p+ nvalue) :=
  scons_p  p ((funcomp) (var_value (p+ nvalue)) (zero_p p)) ((funcomp) (ren_value (shift_p p)) sigma).

Fixpoint subst_value { mvalue : nat } { nvalue : nat } (sigmavalue : (fin) (mvalue) -> value (nvalue)) (s : value (mvalue)) : value (nvalue) :=
    match s with
    | var_value (_) s => sigmavalue s
    | u (_)  => u (nvalue)
    | pair (_) s0 s1 => pair (nvalue) ((subst_value sigmavalue) s0) ((subst_value sigmavalue) s1)
    | inj (_) s0 s1 => inj (nvalue) ((fun x => x) s0) ((subst_value sigmavalue) s1)
    | thunk (_) s0 => thunk (nvalue) ((subst_comp sigmavalue) s0)
    end
 with subst_comp { mvalue : nat } { nvalue : nat } (sigmavalue : (fin) (mvalue) -> value (nvalue)) (s : comp (mvalue)) : comp (nvalue) :=
    match s with
    | cu (_)  => cu (nvalue)
    | force (_) s0 => force (nvalue) ((subst_value sigmavalue) s0)
    | lambda (_) s0 => lambda (nvalue) ((subst_comp (up_value_value sigmavalue)) s0)
    | app (_) s0 s1 => app (nvalue) ((subst_comp sigmavalue) s0) ((subst_value sigmavalue) s1)
    | tuple (_) s0 s1 => tuple (nvalue) ((subst_comp sigmavalue) s0) ((subst_comp sigmavalue) s1)
    | ret (_) s0 => ret (nvalue) ((subst_value sigmavalue) s0)
    | letin (_) s0 s1 => letin (nvalue) ((subst_comp sigmavalue) s0) ((subst_comp (up_value_value sigmavalue)) s1)
    | proj (_) s0 s1 => proj (nvalue) ((fun x => x) s0) ((subst_comp sigmavalue) s1)
    | caseZ (_) s0 => caseZ (nvalue) ((subst_value sigmavalue) s0)
    | caseS (_) s0 s1 s2 => caseS (nvalue) ((subst_value sigmavalue) s0) ((subst_comp (up_value_value sigmavalue)) s1) ((subst_comp (up_value_value sigmavalue)) s2)
    | caseP (_) s0 s1 => caseP (nvalue) ((subst_value sigmavalue) s0) ((subst_comp (up_value_value (up_value_value sigmavalue))) s1)
    end.

Definition upId_value_value { mvalue : nat } (sigma : (fin) (mvalue) -> value (mvalue)) (Eq : forall x, sigma x = (var_value (mvalue)) x) : forall x, (up_value_value sigma) x = (var_value ((S) mvalue)) x :=
  fun n => match n with
  | Some fin_n => (ap) (ren_value (shift)) (Eq fin_n)
  | None => eq_refl
  end.

Definition upIdList_value_value { p : nat } { mvalue : nat } (sigma : (fin) (mvalue) -> value (mvalue)) (Eq : forall x, sigma x = (var_value (mvalue)) x) : forall x, (upList_value_value p sigma) x = (var_value (p+ mvalue)) x :=
  fun n => scons_p_eta (var_value (p+ mvalue)) (fun n => (ap) (ren_value (shift_p p)) (Eq n)) (fun n => eq_refl).

Fixpoint idSubst_value { mvalue : nat } (sigmavalue : (fin) (mvalue) -> value (mvalue)) (Eqvalue : forall x, sigmavalue x = (var_value (mvalue)) x) (s : value (mvalue)) : subst_value sigmavalue s = s :=
    match s with
    | var_value (_) s => Eqvalue s
    | u (_)  => congr_u
    | pair (_) s0 s1 => congr_pair ((idSubst_value sigmavalue Eqvalue) s0) ((idSubst_value sigmavalue Eqvalue) s1)
    | inj (_) s0 s1 => congr_inj ((fun x => (eq_refl) x) s0) ((idSubst_value sigmavalue Eqvalue) s1)
    | thunk (_) s0 => congr_thunk ((idSubst_comp sigmavalue Eqvalue) s0)
    end
 with idSubst_comp { mvalue : nat } (sigmavalue : (fin) (mvalue) -> value (mvalue)) (Eqvalue : forall x, sigmavalue x = (var_value (mvalue)) x) (s : comp (mvalue)) : subst_comp sigmavalue s = s :=
    match s with
    | cu (_)  => congr_cu
    | force (_) s0 => congr_force ((idSubst_value sigmavalue Eqvalue) s0)
    | lambda (_) s0 => congr_lambda ((idSubst_comp (up_value_value sigmavalue) (upId_value_value (_) Eqvalue)) s0)
    | app (_) s0 s1 => congr_app ((idSubst_comp sigmavalue Eqvalue) s0) ((idSubst_value sigmavalue Eqvalue) s1)
    | tuple (_) s0 s1 => congr_tuple ((idSubst_comp sigmavalue Eqvalue) s0) ((idSubst_comp sigmavalue Eqvalue) s1)
    | ret (_) s0 => congr_ret ((idSubst_value sigmavalue Eqvalue) s0)
    | letin (_) s0 s1 => congr_letin ((idSubst_comp sigmavalue Eqvalue) s0) ((idSubst_comp (up_value_value sigmavalue) (upId_value_value (_) Eqvalue)) s1)
    | proj (_) s0 s1 => congr_proj ((fun x => (eq_refl) x) s0) ((idSubst_comp sigmavalue Eqvalue) s1)
    | caseZ (_) s0 => congr_caseZ ((idSubst_value sigmavalue Eqvalue) s0)
    | caseS (_) s0 s1 s2 => congr_caseS ((idSubst_value sigmavalue Eqvalue) s0) ((idSubst_comp (up_value_value sigmavalue) (upId_value_value (_) Eqvalue)) s1) ((idSubst_comp (up_value_value sigmavalue) (upId_value_value (_) Eqvalue)) s2)
    | caseP (_) s0 s1 => congr_caseP ((idSubst_value sigmavalue Eqvalue) s0) ((idSubst_comp (up_value_value (up_value_value sigmavalue)) (upId_value_value (_) (upId_value_value (_) Eqvalue))) s1)
    end.

Definition upExtRen_value_value { m : nat } { n : nat } (xi : (fin) (m) -> (fin) (n)) (zeta : (fin) (m) -> (fin) (n)) (Eq : forall x, xi x = zeta x) : forall x, (upRen_value_value xi) x = (upRen_value_value zeta) x :=
  fun n => match n with
  | Some fin_n => (ap) (shift) (Eq fin_n)
  | None => eq_refl
  end.

Definition upExtRen_list_value_value { p : nat } { m : nat } { n : nat } (xi : (fin) (m) -> (fin) (n)) (zeta : (fin) (m) -> (fin) (n)) (Eq : forall x, xi x = zeta x) : forall x, (upRenList_value_value p xi) x = (upRenList_value_value p zeta) x :=
  fun n => scons_p_congr (fun n => eq_refl) (fun n => (ap) (shift_p p) (Eq n)).

Fixpoint extRen_value { mvalue : nat } { nvalue : nat } (xivalue : (fin) (mvalue) -> (fin) (nvalue)) (zetavalue : (fin) (mvalue) -> (fin) (nvalue)) (Eqvalue : forall x, xivalue x = zetavalue x) (s : value (mvalue)) : ren_value xivalue s = ren_value zetavalue s :=
    match s with
    | var_value (_) s => (ap) (var_value (nvalue)) (Eqvalue s)
    | u (_)  => congr_u
    | pair (_) s0 s1 => congr_pair ((extRen_value xivalue zetavalue Eqvalue) s0) ((extRen_value xivalue zetavalue Eqvalue) s1)
    | inj (_) s0 s1 => congr_inj ((fun x => (eq_refl) x) s0) ((extRen_value xivalue zetavalue Eqvalue) s1)
    | thunk (_) s0 => congr_thunk ((extRen_comp xivalue zetavalue Eqvalue) s0)
    end
 with extRen_comp { mvalue : nat } { nvalue : nat } (xivalue : (fin) (mvalue) -> (fin) (nvalue)) (zetavalue : (fin) (mvalue) -> (fin) (nvalue)) (Eqvalue : forall x, xivalue x = zetavalue x) (s : comp (mvalue)) : ren_comp xivalue s = ren_comp zetavalue s :=
    match s with
    | cu (_)  => congr_cu
    | force (_) s0 => congr_force ((extRen_value xivalue zetavalue Eqvalue) s0)
    | lambda (_) s0 => congr_lambda ((extRen_comp (upRen_value_value xivalue) (upRen_value_value zetavalue) (upExtRen_value_value (_) (_) Eqvalue)) s0)
    | app (_) s0 s1 => congr_app ((extRen_comp xivalue zetavalue Eqvalue) s0) ((extRen_value xivalue zetavalue Eqvalue) s1)
    | tuple (_) s0 s1 => congr_tuple ((extRen_comp xivalue zetavalue Eqvalue) s0) ((extRen_comp xivalue zetavalue Eqvalue) s1)
    | ret (_) s0 => congr_ret ((extRen_value xivalue zetavalue Eqvalue) s0)
    | letin (_) s0 s1 => congr_letin ((extRen_comp xivalue zetavalue Eqvalue) s0) ((extRen_comp (upRen_value_value xivalue) (upRen_value_value zetavalue) (upExtRen_value_value (_) (_) Eqvalue)) s1)
    | proj (_) s0 s1 => congr_proj ((fun x => (eq_refl) x) s0) ((extRen_comp xivalue zetavalue Eqvalue) s1)
    | caseZ (_) s0 => congr_caseZ ((extRen_value xivalue zetavalue Eqvalue) s0)
    | caseS (_) s0 s1 s2 => congr_caseS ((extRen_value xivalue zetavalue Eqvalue) s0) ((extRen_comp (upRen_value_value xivalue) (upRen_value_value zetavalue) (upExtRen_value_value (_) (_) Eqvalue)) s1) ((extRen_comp (upRen_value_value xivalue) (upRen_value_value zetavalue) (upExtRen_value_value (_) (_) Eqvalue)) s2)
    | caseP (_) s0 s1 => congr_caseP ((extRen_value xivalue zetavalue Eqvalue) s0) ((extRen_comp (upRen_value_value (upRen_value_value xivalue)) (upRen_value_value (upRen_value_value zetavalue)) (upExtRen_value_value (_) (_) (upExtRen_value_value (_) (_) Eqvalue))) s1)
    end.

Definition upExt_value_value { m : nat } { nvalue : nat } (sigma : (fin) (m) -> value (nvalue)) (tau : (fin) (m) -> value (nvalue)) (Eq : forall x, sigma x = tau x) : forall x, (up_value_value sigma) x = (up_value_value tau) x :=
  fun n => match n with
  | Some fin_n => (ap) (ren_value (shift)) (Eq fin_n)
  | None => eq_refl
  end.

Definition upExt_list_value_value { p : nat } { m : nat } { nvalue : nat } (sigma : (fin) (m) -> value (nvalue)) (tau : (fin) (m) -> value (nvalue)) (Eq : forall x, sigma x = tau x) : forall x, (upList_value_value p sigma) x = (upList_value_value p tau) x :=
  fun n => scons_p_congr (fun n => eq_refl) (fun n => (ap) (ren_value (shift_p p)) (Eq n)).

Fixpoint ext_value { mvalue : nat } { nvalue : nat } (sigmavalue : (fin) (mvalue) -> value (nvalue)) (tauvalue : (fin) (mvalue) -> value (nvalue)) (Eqvalue : forall x, sigmavalue x = tauvalue x) (s : value (mvalue)) : subst_value sigmavalue s = subst_value tauvalue s :=
    match s with
    | var_value (_) s => Eqvalue s
    | u (_)  => congr_u
    | pair (_) s0 s1 => congr_pair ((ext_value sigmavalue tauvalue Eqvalue) s0) ((ext_value sigmavalue tauvalue Eqvalue) s1)
    | inj (_) s0 s1 => congr_inj ((fun x => (eq_refl) x) s0) ((ext_value sigmavalue tauvalue Eqvalue) s1)
    | thunk (_) s0 => congr_thunk ((ext_comp sigmavalue tauvalue Eqvalue) s0)
    end
 with ext_comp { mvalue : nat } { nvalue : nat } (sigmavalue : (fin) (mvalue) -> value (nvalue)) (tauvalue : (fin) (mvalue) -> value (nvalue)) (Eqvalue : forall x, sigmavalue x = tauvalue x) (s : comp (mvalue)) : subst_comp sigmavalue s = subst_comp tauvalue s :=
    match s with
    | cu (_)  => congr_cu
    | force (_) s0 => congr_force ((ext_value sigmavalue tauvalue Eqvalue) s0)
    | lambda (_) s0 => congr_lambda ((ext_comp (up_value_value sigmavalue) (up_value_value tauvalue) (upExt_value_value (_) (_) Eqvalue)) s0)
    | app (_) s0 s1 => congr_app ((ext_comp sigmavalue tauvalue Eqvalue) s0) ((ext_value sigmavalue tauvalue Eqvalue) s1)
    | tuple (_) s0 s1 => congr_tuple ((ext_comp sigmavalue tauvalue Eqvalue) s0) ((ext_comp sigmavalue tauvalue Eqvalue) s1)
    | ret (_) s0 => congr_ret ((ext_value sigmavalue tauvalue Eqvalue) s0)
    | letin (_) s0 s1 => congr_letin ((ext_comp sigmavalue tauvalue Eqvalue) s0) ((ext_comp (up_value_value sigmavalue) (up_value_value tauvalue) (upExt_value_value (_) (_) Eqvalue)) s1)
    | proj (_) s0 s1 => congr_proj ((fun x => (eq_refl) x) s0) ((ext_comp sigmavalue tauvalue Eqvalue) s1)
    | caseZ (_) s0 => congr_caseZ ((ext_value sigmavalue tauvalue Eqvalue) s0)
    | caseS (_) s0 s1 s2 => congr_caseS ((ext_value sigmavalue tauvalue Eqvalue) s0) ((ext_comp (up_value_value sigmavalue) (up_value_value tauvalue) (upExt_value_value (_) (_) Eqvalue)) s1) ((ext_comp (up_value_value sigmavalue) (up_value_value tauvalue) (upExt_value_value (_) (_) Eqvalue)) s2)
    | caseP (_) s0 s1 => congr_caseP ((ext_value sigmavalue tauvalue Eqvalue) s0) ((ext_comp (up_value_value (up_value_value sigmavalue)) (up_value_value (up_value_value tauvalue)) (upExt_value_value (_) (_) (upExt_value_value (_) (_) Eqvalue))) s1)
    end.

Definition up_ren_ren_value_value { k : nat } { l : nat } { m : nat } (xi : (fin) (k) -> (fin) (l)) (tau : (fin) (l) -> (fin) (m)) (theta : (fin) (k) -> (fin) (m)) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (upRen_value_value tau) (upRen_value_value xi)) x = (upRen_value_value theta) x :=
  up_ren_ren xi tau theta Eq.

Definition up_ren_ren_list_value_value { p : nat } { k : nat } { l : nat } { m : nat } (xi : (fin) (k) -> (fin) (l)) (tau : (fin) (l) -> (fin) (m)) (theta : (fin) (k) -> (fin) (m)) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (upRenList_value_value p tau) (upRenList_value_value p xi)) x = (upRenList_value_value p theta) x :=
  up_ren_ren_p Eq.

Fixpoint compRenRen_value { kvalue : nat } { lvalue : nat } { mvalue : nat } (xivalue : (fin) (mvalue) -> (fin) (kvalue)) (zetavalue : (fin) (kvalue) -> (fin) (lvalue)) (rhovalue : (fin) (mvalue) -> (fin) (lvalue)) (Eqvalue : forall x, ((funcomp) zetavalue xivalue) x = rhovalue x) (s : value (mvalue)) : ren_value zetavalue (ren_value xivalue s) = ren_value rhovalue s :=
    match s with
    | var_value (_) s => (ap) (var_value (lvalue)) (Eqvalue s)
    | u (_)  => congr_u
    | pair (_) s0 s1 => congr_pair ((compRenRen_value xivalue zetavalue rhovalue Eqvalue) s0) ((compRenRen_value xivalue zetavalue rhovalue Eqvalue) s1)
    | inj (_) s0 s1 => congr_inj ((fun x => (eq_refl) x) s0) ((compRenRen_value xivalue zetavalue rhovalue Eqvalue) s1)
    | thunk (_) s0 => congr_thunk ((compRenRen_comp xivalue zetavalue rhovalue Eqvalue) s0)
    end
 with compRenRen_comp { kvalue : nat } { lvalue : nat } { mvalue : nat } (xivalue : (fin) (mvalue) -> (fin) (kvalue)) (zetavalue : (fin) (kvalue) -> (fin) (lvalue)) (rhovalue : (fin) (mvalue) -> (fin) (lvalue)) (Eqvalue : forall x, ((funcomp) zetavalue xivalue) x = rhovalue x) (s : comp (mvalue)) : ren_comp zetavalue (ren_comp xivalue s) = ren_comp rhovalue s :=
    match s with
    | cu (_)  => congr_cu
    | force (_) s0 => congr_force ((compRenRen_value xivalue zetavalue rhovalue Eqvalue) s0)
    | lambda (_) s0 => congr_lambda ((compRenRen_comp (upRen_value_value xivalue) (upRen_value_value zetavalue) (upRen_value_value rhovalue) (up_ren_ren (_) (_) (_) Eqvalue)) s0)
    | app (_) s0 s1 => congr_app ((compRenRen_comp xivalue zetavalue rhovalue Eqvalue) s0) ((compRenRen_value xivalue zetavalue rhovalue Eqvalue) s1)
    | tuple (_) s0 s1 => congr_tuple ((compRenRen_comp xivalue zetavalue rhovalue Eqvalue) s0) ((compRenRen_comp xivalue zetavalue rhovalue Eqvalue) s1)
    | ret (_) s0 => congr_ret ((compRenRen_value xivalue zetavalue rhovalue Eqvalue) s0)
    | letin (_) s0 s1 => congr_letin ((compRenRen_comp xivalue zetavalue rhovalue Eqvalue) s0) ((compRenRen_comp (upRen_value_value xivalue) (upRen_value_value zetavalue) (upRen_value_value rhovalue) (up_ren_ren (_) (_) (_) Eqvalue)) s1)
    | proj (_) s0 s1 => congr_proj ((fun x => (eq_refl) x) s0) ((compRenRen_comp xivalue zetavalue rhovalue Eqvalue) s1)
    | caseZ (_) s0 => congr_caseZ ((compRenRen_value xivalue zetavalue rhovalue Eqvalue) s0)
    | caseS (_) s0 s1 s2 => congr_caseS ((compRenRen_value xivalue zetavalue rhovalue Eqvalue) s0) ((compRenRen_comp (upRen_value_value xivalue) (upRen_value_value zetavalue) (upRen_value_value rhovalue) (up_ren_ren (_) (_) (_) Eqvalue)) s1) ((compRenRen_comp (upRen_value_value xivalue) (upRen_value_value zetavalue) (upRen_value_value rhovalue) (up_ren_ren (_) (_) (_) Eqvalue)) s2)
    | caseP (_) s0 s1 => congr_caseP ((compRenRen_value xivalue zetavalue rhovalue Eqvalue) s0) ((compRenRen_comp (upRen_value_value (upRen_value_value xivalue)) (upRen_value_value (upRen_value_value zetavalue)) (upRen_value_value (upRen_value_value rhovalue)) (up_ren_ren (_) (_) (_) (up_ren_ren (_) (_) (_) Eqvalue))) s1)
    end.

Definition up_ren_subst_value_value { k : nat } { l : nat } { mvalue : nat } (xi : (fin) (k) -> (fin) (l)) (tau : (fin) (l) -> value (mvalue)) (theta : (fin) (k) -> value (mvalue)) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (up_value_value tau) (upRen_value_value xi)) x = (up_value_value theta) x :=
  fun n => match n with
  | Some fin_n => (ap) (ren_value (shift)) (Eq fin_n)
  | None => eq_refl
  end.

Definition up_ren_subst_list_value_value { p : nat } { k : nat } { l : nat } { mvalue : nat } (xi : (fin) (k) -> (fin) (l)) (tau : (fin) (l) -> value (mvalue)) (theta : (fin) (k) -> value (mvalue)) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (upList_value_value p tau) (upRenList_value_value p xi)) x = (upList_value_value p theta) x :=
  fun n => (eq_trans) (scons_p_comp' (_) (_) (_) n) (scons_p_congr (fun z => scons_p_head' (_) (_) z) (fun z => (eq_trans) (scons_p_tail' (_) (_) (xi z)) ((ap) (ren_value (shift_p p)) (Eq z)))).

Fixpoint compRenSubst_value { kvalue : nat } { lvalue : nat } { mvalue : nat } (xivalue : (fin) (mvalue) -> (fin) (kvalue)) (tauvalue : (fin) (kvalue) -> value (lvalue)) (thetavalue : (fin) (mvalue) -> value (lvalue)) (Eqvalue : forall x, ((funcomp) tauvalue xivalue) x = thetavalue x) (s : value (mvalue)) : subst_value tauvalue (ren_value xivalue s) = subst_value thetavalue s :=
    match s with
    | var_value (_) s => Eqvalue s
    | u (_)  => congr_u
    | pair (_) s0 s1 => congr_pair ((compRenSubst_value xivalue tauvalue thetavalue Eqvalue) s0) ((compRenSubst_value xivalue tauvalue thetavalue Eqvalue) s1)
    | inj (_) s0 s1 => congr_inj ((fun x => (eq_refl) x) s0) ((compRenSubst_value xivalue tauvalue thetavalue Eqvalue) s1)
    | thunk (_) s0 => congr_thunk ((compRenSubst_comp xivalue tauvalue thetavalue Eqvalue) s0)
    end
 with compRenSubst_comp { kvalue : nat } { lvalue : nat } { mvalue : nat } (xivalue : (fin) (mvalue) -> (fin) (kvalue)) (tauvalue : (fin) (kvalue) -> value (lvalue)) (thetavalue : (fin) (mvalue) -> value (lvalue)) (Eqvalue : forall x, ((funcomp) tauvalue xivalue) x = thetavalue x) (s : comp (mvalue)) : subst_comp tauvalue (ren_comp xivalue s) = subst_comp thetavalue s :=
    match s with
    | cu (_)  => congr_cu
    | force (_) s0 => congr_force ((compRenSubst_value xivalue tauvalue thetavalue Eqvalue) s0)
    | lambda (_) s0 => congr_lambda ((compRenSubst_comp (upRen_value_value xivalue) (up_value_value tauvalue) (up_value_value thetavalue) (up_ren_subst_value_value (_) (_) (_) Eqvalue)) s0)
    | app (_) s0 s1 => congr_app ((compRenSubst_comp xivalue tauvalue thetavalue Eqvalue) s0) ((compRenSubst_value xivalue tauvalue thetavalue Eqvalue) s1)
    | tuple (_) s0 s1 => congr_tuple ((compRenSubst_comp xivalue tauvalue thetavalue Eqvalue) s0) ((compRenSubst_comp xivalue tauvalue thetavalue Eqvalue) s1)
    | ret (_) s0 => congr_ret ((compRenSubst_value xivalue tauvalue thetavalue Eqvalue) s0)
    | letin (_) s0 s1 => congr_letin ((compRenSubst_comp xivalue tauvalue thetavalue Eqvalue) s0) ((compRenSubst_comp (upRen_value_value xivalue) (up_value_value tauvalue) (up_value_value thetavalue) (up_ren_subst_value_value (_) (_) (_) Eqvalue)) s1)
    | proj (_) s0 s1 => congr_proj ((fun x => (eq_refl) x) s0) ((compRenSubst_comp xivalue tauvalue thetavalue Eqvalue) s1)
    | caseZ (_) s0 => congr_caseZ ((compRenSubst_value xivalue tauvalue thetavalue Eqvalue) s0)
    | caseS (_) s0 s1 s2 => congr_caseS ((compRenSubst_value xivalue tauvalue thetavalue Eqvalue) s0) ((compRenSubst_comp (upRen_value_value xivalue) (up_value_value tauvalue) (up_value_value thetavalue) (up_ren_subst_value_value (_) (_) (_) Eqvalue)) s1) ((compRenSubst_comp (upRen_value_value xivalue) (up_value_value tauvalue) (up_value_value thetavalue) (up_ren_subst_value_value (_) (_) (_) Eqvalue)) s2)
    | caseP (_) s0 s1 => congr_caseP ((compRenSubst_value xivalue tauvalue thetavalue Eqvalue) s0) ((compRenSubst_comp (upRen_value_value (upRen_value_value xivalue)) (up_value_value (up_value_value tauvalue)) (up_value_value (up_value_value thetavalue)) (up_ren_subst_value_value (_) (_) (_) (up_ren_subst_value_value (_) (_) (_) Eqvalue))) s1)
    end.

Definition up_subst_ren_value_value { k : nat } { lvalue : nat } { mvalue : nat } (sigma : (fin) (k) -> value (lvalue)) (zetavalue : (fin) (lvalue) -> (fin) (mvalue)) (theta : (fin) (k) -> value (mvalue)) (Eq : forall x, ((funcomp) (ren_value zetavalue) sigma) x = theta x) : forall x, ((funcomp) (ren_value (upRen_value_value zetavalue)) (up_value_value sigma)) x = (up_value_value theta) x :=
  fun n => match n with
  | Some fin_n => (eq_trans) (compRenRen_value (shift) (upRen_value_value zetavalue) ((funcomp) (shift) zetavalue) (fun x => eq_refl) (sigma fin_n)) ((eq_trans) ((eq_sym) (compRenRen_value zetavalue (shift) ((funcomp) (shift) zetavalue) (fun x => eq_refl) (sigma fin_n))) ((ap) (ren_value (shift)) (Eq fin_n)))
  | None => eq_refl
  end.

Definition up_subst_ren_list_value_value { p : nat } { k : nat } { lvalue : nat } { mvalue : nat } (sigma : (fin) (k) -> value (lvalue)) (zetavalue : (fin) (lvalue) -> (fin) (mvalue)) (theta : (fin) (k) -> value (mvalue)) (Eq : forall x, ((funcomp) (ren_value zetavalue) sigma) x = theta x) : forall x, ((funcomp) (ren_value (upRenList_value_value p zetavalue)) (upList_value_value p sigma)) x = (upList_value_value p theta) x :=
  fun n => (eq_trans) (scons_p_comp' (_) (_) (_) n) (scons_p_congr (fun x => (ap) (var_value (p+ mvalue)) (scons_p_head' (_) (_) x)) (fun n => (eq_trans) (compRenRen_value (shift_p p) (upRenList_value_value p zetavalue) ((funcomp) (shift_p p) zetavalue) (fun x => scons_p_tail' (_) (_) x) (sigma n)) ((eq_trans) ((eq_sym) (compRenRen_value zetavalue (shift_p p) ((funcomp) (shift_p p) zetavalue) (fun x => eq_refl) (sigma n))) ((ap) (ren_value (shift_p p)) (Eq n))))).

Fixpoint compSubstRen_value { kvalue : nat } { lvalue : nat } { mvalue : nat } (sigmavalue : (fin) (mvalue) -> value (kvalue)) (zetavalue : (fin) (kvalue) -> (fin) (lvalue)) (thetavalue : (fin) (mvalue) -> value (lvalue)) (Eqvalue : forall x, ((funcomp) (ren_value zetavalue) sigmavalue) x = thetavalue x) (s : value (mvalue)) : ren_value zetavalue (subst_value sigmavalue s) = subst_value thetavalue s :=
    match s with
    | var_value (_) s => Eqvalue s
    | u (_)  => congr_u
    | pair (_) s0 s1 => congr_pair ((compSubstRen_value sigmavalue zetavalue thetavalue Eqvalue) s0) ((compSubstRen_value sigmavalue zetavalue thetavalue Eqvalue) s1)
    | inj (_) s0 s1 => congr_inj ((fun x => (eq_refl) x) s0) ((compSubstRen_value sigmavalue zetavalue thetavalue Eqvalue) s1)
    | thunk (_) s0 => congr_thunk ((compSubstRen_comp sigmavalue zetavalue thetavalue Eqvalue) s0)
    end
 with compSubstRen_comp { kvalue : nat } { lvalue : nat } { mvalue : nat } (sigmavalue : (fin) (mvalue) -> value (kvalue)) (zetavalue : (fin) (kvalue) -> (fin) (lvalue)) (thetavalue : (fin) (mvalue) -> value (lvalue)) (Eqvalue : forall x, ((funcomp) (ren_value zetavalue) sigmavalue) x = thetavalue x) (s : comp (mvalue)) : ren_comp zetavalue (subst_comp sigmavalue s) = subst_comp thetavalue s :=
    match s with
    | cu (_)  => congr_cu
    | force (_) s0 => congr_force ((compSubstRen_value sigmavalue zetavalue thetavalue Eqvalue) s0)
    | lambda (_) s0 => congr_lambda ((compSubstRen_comp (up_value_value sigmavalue) (upRen_value_value zetavalue) (up_value_value thetavalue) (up_subst_ren_value_value (_) (_) (_) Eqvalue)) s0)
    | app (_) s0 s1 => congr_app ((compSubstRen_comp sigmavalue zetavalue thetavalue Eqvalue) s0) ((compSubstRen_value sigmavalue zetavalue thetavalue Eqvalue) s1)
    | tuple (_) s0 s1 => congr_tuple ((compSubstRen_comp sigmavalue zetavalue thetavalue Eqvalue) s0) ((compSubstRen_comp sigmavalue zetavalue thetavalue Eqvalue) s1)
    | ret (_) s0 => congr_ret ((compSubstRen_value sigmavalue zetavalue thetavalue Eqvalue) s0)
    | letin (_) s0 s1 => congr_letin ((compSubstRen_comp sigmavalue zetavalue thetavalue Eqvalue) s0) ((compSubstRen_comp (up_value_value sigmavalue) (upRen_value_value zetavalue) (up_value_value thetavalue) (up_subst_ren_value_value (_) (_) (_) Eqvalue)) s1)
    | proj (_) s0 s1 => congr_proj ((fun x => (eq_refl) x) s0) ((compSubstRen_comp sigmavalue zetavalue thetavalue Eqvalue) s1)
    | caseZ (_) s0 => congr_caseZ ((compSubstRen_value sigmavalue zetavalue thetavalue Eqvalue) s0)
    | caseS (_) s0 s1 s2 => congr_caseS ((compSubstRen_value sigmavalue zetavalue thetavalue Eqvalue) s0) ((compSubstRen_comp (up_value_value sigmavalue) (upRen_value_value zetavalue) (up_value_value thetavalue) (up_subst_ren_value_value (_) (_) (_) Eqvalue)) s1) ((compSubstRen_comp (up_value_value sigmavalue) (upRen_value_value zetavalue) (up_value_value thetavalue) (up_subst_ren_value_value (_) (_) (_) Eqvalue)) s2)
    | caseP (_) s0 s1 => congr_caseP ((compSubstRen_value sigmavalue zetavalue thetavalue Eqvalue) s0) ((compSubstRen_comp (up_value_value (up_value_value sigmavalue)) (upRen_value_value (upRen_value_value zetavalue)) (up_value_value (up_value_value thetavalue)) (up_subst_ren_value_value (_) (_) (_) (up_subst_ren_value_value (_) (_) (_) Eqvalue))) s1)
    end.

Definition up_subst_subst_value_value { k : nat } { lvalue : nat } { mvalue : nat } (sigma : (fin) (k) -> value (lvalue)) (tauvalue : (fin) (lvalue) -> value (mvalue)) (theta : (fin) (k) -> value (mvalue)) (Eq : forall x, ((funcomp) (subst_value tauvalue) sigma) x = theta x) : forall x, ((funcomp) (subst_value (up_value_value tauvalue)) (up_value_value sigma)) x = (up_value_value theta) x :=
  fun n => match n with
  | Some fin_n => (eq_trans) (compRenSubst_value (shift) (up_value_value tauvalue) ((funcomp) (up_value_value tauvalue) (shift)) (fun x => eq_refl) (sigma fin_n)) ((eq_trans) ((eq_sym) (compSubstRen_value tauvalue (shift) ((funcomp) (ren_value (shift)) tauvalue) (fun x => eq_refl) (sigma fin_n))) ((ap) (ren_value (shift)) (Eq fin_n)))
  | None => eq_refl
  end.

Definition up_subst_subst_list_value_value { p : nat } { k : nat } { lvalue : nat } { mvalue : nat } (sigma : (fin) (k) -> value (lvalue)) (tauvalue : (fin) (lvalue) -> value (mvalue)) (theta : (fin) (k) -> value (mvalue)) (Eq : forall x, ((funcomp) (subst_value tauvalue) sigma) x = theta x) : forall x, ((funcomp) (subst_value (upList_value_value p tauvalue)) (upList_value_value p sigma)) x = (upList_value_value p theta) x :=
  fun n => (eq_trans) (scons_p_comp' ((funcomp) (var_value (p+ lvalue)) (zero_p p)) (_) (_) n) (scons_p_congr (fun x => scons_p_head' (_) (fun z => ren_value (shift_p p) (_)) x) (fun n => (eq_trans) (compRenSubst_value (shift_p p) (upList_value_value p tauvalue) ((funcomp) (upList_value_value p tauvalue) (shift_p p)) (fun x => eq_refl) (sigma n)) ((eq_trans) ((eq_sym) (compSubstRen_value tauvalue (shift_p p) (_) (fun x => (eq_sym) (scons_p_tail' (_) (_) x)) (sigma n))) ((ap) (ren_value (shift_p p)) (Eq n))))).

Fixpoint compSubstSubst_value { kvalue : nat } { lvalue : nat } { mvalue : nat } (sigmavalue : (fin) (mvalue) -> value (kvalue)) (tauvalue : (fin) (kvalue) -> value (lvalue)) (thetavalue : (fin) (mvalue) -> value (lvalue)) (Eqvalue : forall x, ((funcomp) (subst_value tauvalue) sigmavalue) x = thetavalue x) (s : value (mvalue)) : subst_value tauvalue (subst_value sigmavalue s) = subst_value thetavalue s :=
    match s with
    | var_value (_) s => Eqvalue s
    | u (_)  => congr_u
    | pair (_) s0 s1 => congr_pair ((compSubstSubst_value sigmavalue tauvalue thetavalue Eqvalue) s0) ((compSubstSubst_value sigmavalue tauvalue thetavalue Eqvalue) s1)
    | inj (_) s0 s1 => congr_inj ((fun x => (eq_refl) x) s0) ((compSubstSubst_value sigmavalue tauvalue thetavalue Eqvalue) s1)
    | thunk (_) s0 => congr_thunk ((compSubstSubst_comp sigmavalue tauvalue thetavalue Eqvalue) s0)
    end
 with compSubstSubst_comp { kvalue : nat } { lvalue : nat } { mvalue : nat } (sigmavalue : (fin) (mvalue) -> value (kvalue)) (tauvalue : (fin) (kvalue) -> value (lvalue)) (thetavalue : (fin) (mvalue) -> value (lvalue)) (Eqvalue : forall x, ((funcomp) (subst_value tauvalue) sigmavalue) x = thetavalue x) (s : comp (mvalue)) : subst_comp tauvalue (subst_comp sigmavalue s) = subst_comp thetavalue s :=
    match s with
    | cu (_)  => congr_cu
    | force (_) s0 => congr_force ((compSubstSubst_value sigmavalue tauvalue thetavalue Eqvalue) s0)
    | lambda (_) s0 => congr_lambda ((compSubstSubst_comp (up_value_value sigmavalue) (up_value_value tauvalue) (up_value_value thetavalue) (up_subst_subst_value_value (_) (_) (_) Eqvalue)) s0)
    | app (_) s0 s1 => congr_app ((compSubstSubst_comp sigmavalue tauvalue thetavalue Eqvalue) s0) ((compSubstSubst_value sigmavalue tauvalue thetavalue Eqvalue) s1)
    | tuple (_) s0 s1 => congr_tuple ((compSubstSubst_comp sigmavalue tauvalue thetavalue Eqvalue) s0) ((compSubstSubst_comp sigmavalue tauvalue thetavalue Eqvalue) s1)
    | ret (_) s0 => congr_ret ((compSubstSubst_value sigmavalue tauvalue thetavalue Eqvalue) s0)
    | letin (_) s0 s1 => congr_letin ((compSubstSubst_comp sigmavalue tauvalue thetavalue Eqvalue) s0) ((compSubstSubst_comp (up_value_value sigmavalue) (up_value_value tauvalue) (up_value_value thetavalue) (up_subst_subst_value_value (_) (_) (_) Eqvalue)) s1)
    | proj (_) s0 s1 => congr_proj ((fun x => (eq_refl) x) s0) ((compSubstSubst_comp sigmavalue tauvalue thetavalue Eqvalue) s1)
    | caseZ (_) s0 => congr_caseZ ((compSubstSubst_value sigmavalue tauvalue thetavalue Eqvalue) s0)
    | caseS (_) s0 s1 s2 => congr_caseS ((compSubstSubst_value sigmavalue tauvalue thetavalue Eqvalue) s0) ((compSubstSubst_comp (up_value_value sigmavalue) (up_value_value tauvalue) (up_value_value thetavalue) (up_subst_subst_value_value (_) (_) (_) Eqvalue)) s1) ((compSubstSubst_comp (up_value_value sigmavalue) (up_value_value tauvalue) (up_value_value thetavalue) (up_subst_subst_value_value (_) (_) (_) Eqvalue)) s2)
    | caseP (_) s0 s1 => congr_caseP ((compSubstSubst_value sigmavalue tauvalue thetavalue Eqvalue) s0) ((compSubstSubst_comp (up_value_value (up_value_value sigmavalue)) (up_value_value (up_value_value tauvalue)) (up_value_value (up_value_value thetavalue)) (up_subst_subst_value_value (_) (_) (_) (up_subst_subst_value_value (_) (_) (_) Eqvalue))) s1)
    end.

Definition rinstInst_up_value_value { m : nat } { nvalue : nat } (xi : (fin) (m) -> (fin) (nvalue)) (sigma : (fin) (m) -> value (nvalue)) (Eq : forall x, ((funcomp) (var_value (nvalue)) xi) x = sigma x) : forall x, ((funcomp) (var_value ((S) nvalue)) (upRen_value_value xi)) x = (up_value_value sigma) x :=
  fun n => match n with
  | Some fin_n => (ap) (ren_value (shift)) (Eq fin_n)
  | None => eq_refl
  end.

Definition rinstInst_up_list_value_value { p : nat } { m : nat } { nvalue : nat } (xi : (fin) (m) -> (fin) (nvalue)) (sigma : (fin) (m) -> value (nvalue)) (Eq : forall x, ((funcomp) (var_value (nvalue)) xi) x = sigma x) : forall x, ((funcomp) (var_value (p+ nvalue)) (upRenList_value_value p xi)) x = (upList_value_value p sigma) x :=
  fun n => (eq_trans) (scons_p_comp' (_) (_) (var_value (p+ nvalue)) n) (scons_p_congr (fun z => eq_refl) (fun n => (ap) (ren_value (shift_p p)) (Eq n))).

Fixpoint rinst_inst_value { mvalue : nat } { nvalue : nat } (xivalue : (fin) (mvalue) -> (fin) (nvalue)) (sigmavalue : (fin) (mvalue) -> value (nvalue)) (Eqvalue : forall x, ((funcomp) (var_value (nvalue)) xivalue) x = sigmavalue x) (s : value (mvalue)) : ren_value xivalue s = subst_value sigmavalue s :=
    match s with
    | var_value (_) s => Eqvalue s
    | u (_)  => congr_u
    | pair (_) s0 s1 => congr_pair ((rinst_inst_value xivalue sigmavalue Eqvalue) s0) ((rinst_inst_value xivalue sigmavalue Eqvalue) s1)
    | inj (_) s0 s1 => congr_inj ((fun x => (eq_refl) x) s0) ((rinst_inst_value xivalue sigmavalue Eqvalue) s1)
    | thunk (_) s0 => congr_thunk ((rinst_inst_comp xivalue sigmavalue Eqvalue) s0)
    end
 with rinst_inst_comp { mvalue : nat } { nvalue : nat } (xivalue : (fin) (mvalue) -> (fin) (nvalue)) (sigmavalue : (fin) (mvalue) -> value (nvalue)) (Eqvalue : forall x, ((funcomp) (var_value (nvalue)) xivalue) x = sigmavalue x) (s : comp (mvalue)) : ren_comp xivalue s = subst_comp sigmavalue s :=
    match s with
    | cu (_)  => congr_cu
    | force (_) s0 => congr_force ((rinst_inst_value xivalue sigmavalue Eqvalue) s0)
    | lambda (_) s0 => congr_lambda ((rinst_inst_comp (upRen_value_value xivalue) (up_value_value sigmavalue) (rinstInst_up_value_value (_) (_) Eqvalue)) s0)
    | app (_) s0 s1 => congr_app ((rinst_inst_comp xivalue sigmavalue Eqvalue) s0) ((rinst_inst_value xivalue sigmavalue Eqvalue) s1)
    | tuple (_) s0 s1 => congr_tuple ((rinst_inst_comp xivalue sigmavalue Eqvalue) s0) ((rinst_inst_comp xivalue sigmavalue Eqvalue) s1)
    | ret (_) s0 => congr_ret ((rinst_inst_value xivalue sigmavalue Eqvalue) s0)
    | letin (_) s0 s1 => congr_letin ((rinst_inst_comp xivalue sigmavalue Eqvalue) s0) ((rinst_inst_comp (upRen_value_value xivalue) (up_value_value sigmavalue) (rinstInst_up_value_value (_) (_) Eqvalue)) s1)
    | proj (_) s0 s1 => congr_proj ((fun x => (eq_refl) x) s0) ((rinst_inst_comp xivalue sigmavalue Eqvalue) s1)
    | caseZ (_) s0 => congr_caseZ ((rinst_inst_value xivalue sigmavalue Eqvalue) s0)
    | caseS (_) s0 s1 s2 => congr_caseS ((rinst_inst_value xivalue sigmavalue Eqvalue) s0) ((rinst_inst_comp (upRen_value_value xivalue) (up_value_value sigmavalue) (rinstInst_up_value_value (_) (_) Eqvalue)) s1) ((rinst_inst_comp (upRen_value_value xivalue) (up_value_value sigmavalue) (rinstInst_up_value_value (_) (_) Eqvalue)) s2)
    | caseP (_) s0 s1 => congr_caseP ((rinst_inst_value xivalue sigmavalue Eqvalue) s0) ((rinst_inst_comp (upRen_value_value (upRen_value_value xivalue)) (up_value_value (up_value_value sigmavalue)) (rinstInst_up_value_value (_) (_) (rinstInst_up_value_value (_) (_) Eqvalue))) s1)
    end.

Lemma rinstInst_value { mvalue : nat } { nvalue : nat } (xivalue : (fin) (mvalue) -> (fin) (nvalue)) : ren_value xivalue = subst_value ((funcomp) (var_value (nvalue)) xivalue) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => rinst_inst_value xivalue (_) (fun n => eq_refl) x)). Qed.

Lemma rinstInst_comp { mvalue : nat } { nvalue : nat } (xivalue : (fin) (mvalue) -> (fin) (nvalue)) : ren_comp xivalue = subst_comp ((funcomp) (var_value (nvalue)) xivalue) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => rinst_inst_comp xivalue (_) (fun n => eq_refl) x)). Qed.

Lemma instId_value { mvalue : nat } : subst_value (var_value (mvalue)) = id .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_value (var_value (mvalue)) (fun n => eq_refl) ((id) x))). Qed.

Lemma instId_comp { mvalue : nat } : subst_comp (var_value (mvalue)) = id .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_comp (var_value (mvalue)) (fun n => eq_refl) ((id) x))). Qed.

Lemma rinstId_value { mvalue : nat } : @ren_value (mvalue) (mvalue) (id) = id .
Proof. exact ((eq_trans) (rinstInst_value ((id) (_))) instId_value). Qed.

Lemma rinstId_comp { mvalue : nat } : @ren_comp (mvalue) (mvalue) (id) = id .
Proof. exact ((eq_trans) (rinstInst_comp ((id) (_))) instId_comp). Qed.

Lemma varL_value { mvalue : nat } { nvalue : nat } (sigmavalue : (fin) (mvalue) -> value (nvalue)) : (funcomp) (subst_value sigmavalue) (var_value (mvalue)) = sigmavalue .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => eq_refl)). Qed.

Lemma varLRen_value { mvalue : nat } { nvalue : nat } (xivalue : (fin) (mvalue) -> (fin) (nvalue)) : (funcomp) (ren_value xivalue) (var_value (mvalue)) = (funcomp) (var_value (nvalue)) xivalue .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => eq_refl)). Qed.

Lemma compComp_value { kvalue : nat } { lvalue : nat } { mvalue : nat } (sigmavalue : (fin) (mvalue) -> value (kvalue)) (tauvalue : (fin) (kvalue) -> value (lvalue)) (s : value (mvalue)) : subst_value tauvalue (subst_value sigmavalue s) = subst_value ((funcomp) (subst_value tauvalue) sigmavalue) s .
Proof. exact (compSubstSubst_value sigmavalue tauvalue (_) (fun n => eq_refl) s). Qed.

Lemma compComp_comp { kvalue : nat } { lvalue : nat } { mvalue : nat } (sigmavalue : (fin) (mvalue) -> value (kvalue)) (tauvalue : (fin) (kvalue) -> value (lvalue)) (s : comp (mvalue)) : subst_comp tauvalue (subst_comp sigmavalue s) = subst_comp ((funcomp) (subst_value tauvalue) sigmavalue) s .
Proof. exact (compSubstSubst_comp sigmavalue tauvalue (_) (fun n => eq_refl) s). Qed.

Lemma compComp'_value { kvalue : nat } { lvalue : nat } { mvalue : nat } (sigmavalue : (fin) (mvalue) -> value (kvalue)) (tauvalue : (fin) (kvalue) -> value (lvalue)) : (funcomp) (subst_value tauvalue) (subst_value sigmavalue) = subst_value ((funcomp) (subst_value tauvalue) sigmavalue) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_value sigmavalue tauvalue n)). Qed.

Lemma compComp'_comp { kvalue : nat } { lvalue : nat } { mvalue : nat } (sigmavalue : (fin) (mvalue) -> value (kvalue)) (tauvalue : (fin) (kvalue) -> value (lvalue)) : (funcomp) (subst_comp tauvalue) (subst_comp sigmavalue) = subst_comp ((funcomp) (subst_value tauvalue) sigmavalue) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_comp sigmavalue tauvalue n)). Qed.

Lemma compRen_value { kvalue : nat } { lvalue : nat } { mvalue : nat } (sigmavalue : (fin) (mvalue) -> value (kvalue)) (zetavalue : (fin) (kvalue) -> (fin) (lvalue)) (s : value (mvalue)) : ren_value zetavalue (subst_value sigmavalue s) = subst_value ((funcomp) (ren_value zetavalue) sigmavalue) s .
Proof. exact (compSubstRen_value sigmavalue zetavalue (_) (fun n => eq_refl) s). Qed.

Lemma compRen_comp { kvalue : nat } { lvalue : nat } { mvalue : nat } (sigmavalue : (fin) (mvalue) -> value (kvalue)) (zetavalue : (fin) (kvalue) -> (fin) (lvalue)) (s : comp (mvalue)) : ren_comp zetavalue (subst_comp sigmavalue s) = subst_comp ((funcomp) (ren_value zetavalue) sigmavalue) s .
Proof. exact (compSubstRen_comp sigmavalue zetavalue (_) (fun n => eq_refl) s). Qed.

Lemma compRen'_value { kvalue : nat } { lvalue : nat } { mvalue : nat } (sigmavalue : (fin) (mvalue) -> value (kvalue)) (zetavalue : (fin) (kvalue) -> (fin) (lvalue)) : (funcomp) (ren_value zetavalue) (subst_value sigmavalue) = subst_value ((funcomp) (ren_value zetavalue) sigmavalue) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compRen_value sigmavalue zetavalue n)). Qed.

Lemma compRen'_comp { kvalue : nat } { lvalue : nat } { mvalue : nat } (sigmavalue : (fin) (mvalue) -> value (kvalue)) (zetavalue : (fin) (kvalue) -> (fin) (lvalue)) : (funcomp) (ren_comp zetavalue) (subst_comp sigmavalue) = subst_comp ((funcomp) (ren_value zetavalue) sigmavalue) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compRen_comp sigmavalue zetavalue n)). Qed.

Lemma renComp_value { kvalue : nat } { lvalue : nat } { mvalue : nat } (xivalue : (fin) (mvalue) -> (fin) (kvalue)) (tauvalue : (fin) (kvalue) -> value (lvalue)) (s : value (mvalue)) : subst_value tauvalue (ren_value xivalue s) = subst_value ((funcomp) tauvalue xivalue) s .
Proof. exact (compRenSubst_value xivalue tauvalue (_) (fun n => eq_refl) s). Qed.

Lemma renComp_comp { kvalue : nat } { lvalue : nat } { mvalue : nat } (xivalue : (fin) (mvalue) -> (fin) (kvalue)) (tauvalue : (fin) (kvalue) -> value (lvalue)) (s : comp (mvalue)) : subst_comp tauvalue (ren_comp xivalue s) = subst_comp ((funcomp) tauvalue xivalue) s .
Proof. exact (compRenSubst_comp xivalue tauvalue (_) (fun n => eq_refl) s). Qed.

Lemma renComp'_value { kvalue : nat } { lvalue : nat } { mvalue : nat } (xivalue : (fin) (mvalue) -> (fin) (kvalue)) (tauvalue : (fin) (kvalue) -> value (lvalue)) : (funcomp) (subst_value tauvalue) (ren_value xivalue) = subst_value ((funcomp) tauvalue xivalue) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renComp_value xivalue tauvalue n)). Qed.

Lemma renComp'_comp { kvalue : nat } { lvalue : nat } { mvalue : nat } (xivalue : (fin) (mvalue) -> (fin) (kvalue)) (tauvalue : (fin) (kvalue) -> value (lvalue)) : (funcomp) (subst_comp tauvalue) (ren_comp xivalue) = subst_comp ((funcomp) tauvalue xivalue) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renComp_comp xivalue tauvalue n)). Qed.

Lemma renRen_value { kvalue : nat } { lvalue : nat } { mvalue : nat } (xivalue : (fin) (mvalue) -> (fin) (kvalue)) (zetavalue : (fin) (kvalue) -> (fin) (lvalue)) (s : value (mvalue)) : ren_value zetavalue (ren_value xivalue s) = ren_value ((funcomp) zetavalue xivalue) s .
Proof. exact (compRenRen_value xivalue zetavalue (_) (fun n => eq_refl) s). Qed.

Lemma renRen_comp { kvalue : nat } { lvalue : nat } { mvalue : nat } (xivalue : (fin) (mvalue) -> (fin) (kvalue)) (zetavalue : (fin) (kvalue) -> (fin) (lvalue)) (s : comp (mvalue)) : ren_comp zetavalue (ren_comp xivalue s) = ren_comp ((funcomp) zetavalue xivalue) s .
Proof. exact (compRenRen_comp xivalue zetavalue (_) (fun n => eq_refl) s). Qed.

Lemma renRen'_value { kvalue : nat } { lvalue : nat } { mvalue : nat } (xivalue : (fin) (mvalue) -> (fin) (kvalue)) (zetavalue : (fin) (kvalue) -> (fin) (lvalue)) : (funcomp) (ren_value zetavalue) (ren_value xivalue) = ren_value ((funcomp) zetavalue xivalue) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renRen_value xivalue zetavalue n)). Qed.

Lemma renRen'_comp { kvalue : nat } { lvalue : nat } { mvalue : nat } (xivalue : (fin) (mvalue) -> (fin) (kvalue)) (zetavalue : (fin) (kvalue) -> (fin) (lvalue)) : (funcomp) (ren_comp zetavalue) (ren_comp xivalue) = ren_comp ((funcomp) zetavalue xivalue) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renRen_comp xivalue zetavalue n)). Qed.

End valuecomp.

Arguments var_value {nvalue}.

Arguments u {nvalue}.

Arguments pair {nvalue}.

Arguments inj {nvalue}.

Arguments thunk {nvalue}.

Arguments cu {nvalue}.

Arguments force {nvalue}.

Arguments lambda {nvalue}.

Arguments app {nvalue}.

Arguments tuple {nvalue}.

Arguments ret {nvalue}.

Arguments letin {nvalue}.

Arguments proj {nvalue}.

Arguments caseZ {nvalue}.

Arguments caseS {nvalue}.

Arguments caseP {nvalue}.

Global Instance Subst_value { mvalue : nat } { nvalue : nat } : Subst1 ((fin) (mvalue) -> value (nvalue)) (value (mvalue)) (value (nvalue)) := @subst_value (mvalue) (nvalue) .

Global Instance Subst_comp { mvalue : nat } { nvalue : nat } : Subst1 ((fin) (mvalue) -> value (nvalue)) (comp (mvalue)) (comp (nvalue)) := @subst_comp (mvalue) (nvalue) .

Global Instance Ren_value { mvalue : nat } { nvalue : nat } : Ren1 ((fin) (mvalue) -> (fin) (nvalue)) (value (mvalue)) (value (nvalue)) := @ren_value (mvalue) (nvalue) .

Global Instance Ren_comp { mvalue : nat } { nvalue : nat } : Ren1 ((fin) (mvalue) -> (fin) (nvalue)) (comp (mvalue)) (comp (nvalue)) := @ren_comp (mvalue) (nvalue) .

Global Instance VarInstance_value { mvalue : nat } : Var ((fin) (mvalue)) (value (mvalue)) := @var_value (mvalue) .

Notation "x '__value'" := (var_value x) (at level 5, format "x __value") : subst_scope.

Notation "x '__value'" := (@ids (_) (_) VarInstance_value x) (at level 5, only printing, format "x __value") : subst_scope.

Notation "'var'" := (var_value) (only printing, at level 1) : subst_scope.

Class Up_value X Y := up_value : X -> Y.

Notation "↑__value" := (up_value) (only printing) : subst_scope.

Notation "↑__value" := (up_value_value) (only printing) : subst_scope.

Global Instance Up_value_value { m : nat } { nvalue : nat } : Up_value (_) (_) := @up_value_value (m) (nvalue) .

(* Notation "s [ sigmavalue ]" := (subst_value sigmavalue s) (at level 7, left associativity, only printing) : subst_scope. *)

(* Notation "[ sigmavalue ]" := (subst_value sigmavalue) (at level 1, left associativity, only printing) : fscope. *)

(* Notation "s ⟨ xivalue ⟩" := (ren_value xivalue s) (at level 7, left associativity, only printing) : subst_scope. *)

Notation "⟨ xivalue ⟩" := (ren_value xivalue) (at level 1, left associativity, only printing) : fscope.

(* Notation "s [ sigmavalue ]" := (subst_comp sigmavalue s) (at level 7, left associativity, only printing) : subst_scope. *)

(* Notation "[ sigmavalue ]" := (subst_comp sigmavalue) (at level 1, left associativity, only printing) : fscope. *)

(* Notation "s ⟨ xivalue ⟩" := (ren_comp xivalue s) (at level 7, left associativity, only printing) : subst_scope. *)

Notation "⟨ xivalue ⟩" := (ren_comp xivalue) (at level 1, left associativity, only printing) : fscope.

Ltac auto_unfold := repeat unfold subst1,  subst2,  Subst1,  Subst2,  ids,  ren1,  ren2,  Ren1,  Ren2,  Subst_value,  Subst_comp,  Ren_value,  Ren_comp,  VarInstance_value.

Tactic Notation "auto_unfold" "in" "*" := repeat unfold subst1,  subst2,  Subst1,  Subst2,  ids,  ren1,  ren2,  Ren1,  Ren2,  Subst_value,  Subst_comp,  Ren_value,  Ren_comp,  VarInstance_value in *.

Ltac asimpl' := repeat first [progress rewrite ?instId_value| progress rewrite ?compComp_value| progress rewrite ?compComp'_value| progress rewrite ?instId_comp| progress rewrite ?compComp_comp| progress rewrite ?compComp'_comp| progress rewrite ?rinstId_value| progress rewrite ?compRen_value| progress rewrite ?compRen'_value| progress rewrite ?renComp_value| progress rewrite ?renComp'_value| progress rewrite ?renRen_value| progress rewrite ?renRen'_value| progress rewrite ?rinstId_comp| progress rewrite ?compRen_comp| progress rewrite ?compRen'_comp| progress rewrite ?renComp_comp| progress rewrite ?renComp'_comp| progress rewrite ?renRen_comp| progress rewrite ?renRen'_comp| progress rewrite ?varL_value| progress rewrite ?varLRen_value| progress (unfold up_ren, upRen_value_value, upRenList_value_value, up_value_value, upList_value_value)| progress (cbn [subst_value subst_comp ren_value ren_comp])| fsimpl].

Ltac asimpl := repeat try unfold_funcomp; auto_unfold in *; asimpl'; repeat try unfold_funcomp.

Tactic Notation "asimpl" "in" hyp(J) := revert J; asimpl; intros J.

Tactic Notation "auto_case" := auto_case (asimpl; cbn; eauto).

Tactic Notation "asimpl" "in" "*" := auto_unfold in *; repeat first [progress rewrite ?instId_value in *| progress rewrite ?compComp_value in *| progress rewrite ?compComp'_value in *| progress rewrite ?instId_comp in *| progress rewrite ?compComp_comp in *| progress rewrite ?compComp'_comp in *| progress rewrite ?rinstId_value in *| progress rewrite ?compRen_value in *| progress rewrite ?compRen'_value in *| progress rewrite ?renComp_value in *| progress rewrite ?renComp'_value in *| progress rewrite ?renRen_value in *| progress rewrite ?renRen'_value in *| progress rewrite ?rinstId_comp in *| progress rewrite ?compRen_comp in *| progress rewrite ?compRen'_comp in *| progress rewrite ?renComp_comp in *| progress rewrite ?renComp'_comp in *| progress rewrite ?renRen_comp in *| progress rewrite ?renRen'_comp in *| progress rewrite ?varL_value in *| progress rewrite ?varLRen_value in *| progress (unfold up_ren, upRen_value_value, upRenList_value_value, up_value_value, upList_value_value in *)| progress (cbn [subst_value subst_comp ren_value ren_comp] in *)| fsimpl in *].

Ltac substify := auto_unfold; try repeat (erewrite rinstInst_value); try repeat (erewrite rinstInst_comp).

Ltac renamify := auto_unfold; try repeat (erewrite <- rinstInst_value); try repeat (erewrite <- rinstInst_comp).
