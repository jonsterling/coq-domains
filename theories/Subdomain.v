From Coq Require Import ssrbool.
From mathcomp Require Import ssrnat.
From Domains Require Import Preamble Preorder Poset Dcpo DcpoExponential Kleene Lift Sierpinski.

Set Bullet Behavior "Strict Subproofs".

Definition has_dlub {D : Poset.type} (S : D → Prop) :=
  ∀ (A : Family D), is_directed A → (∀ x, S (A x)) → ∀ x, is_lub A x → S x.

Definition has_pdlub {D : Poset.type} (S : D → Prop) :=
  ∀ (A : Family D), is_predirected A → (∀ x, S (A x)) → ∀ x, is_lub A x → S x.

Definition has_bot {D : Poset.type} (S : D → Prop) :=
  ∀ x, is_bottom x → S x.

Definition admissible {D : Poset.type} (S : D → Prop) :=
  has_bot S ∧ has_dlub S.


Lemma admiss_has_bot {D : Poset.type} (S : D → Prop) : admissible S → has_bot S.
Proof. by case. Qed.

Lemma admiss_has_dlub {D : Poset.type} (S : D → Prop) : admissible S → has_dlub S.
Proof. by case. Qed.

Definition fam_adjoin_elt {D : Poset.type} (A : Family D) (x : D) : Family D.
Proof.
  exists (sum True (fam_ix A)); case.
  - by move=> _; exact: x.
  - by apply: A.
Defined.

Lemma fam_adjoin_bot_directed {D : PointedPoset.type} (A : Family D) (hA : is_predirected A) : is_directed (fam_adjoin_elt A ⊥).
Proof.
  split.
  - by unshelve esplit; first by left.
  - case; simpl.
    + case.
      * case; first by exists (inl I).
        move=> i.
        by exists (inr i); split.
    + move=> i; case.
      * by case; exists (inr i); split.
      * move=> j.
        case: (hA i j)=> k h.
        by exists (inr k).
Qed.

Lemma fam_adjoin_bot_same_lub {D : PointedPoset.type} (A : Family D) : is_lub A = is_lub (fam_adjoin_elt A ⊥).
Proof.
  apply: funext=> x; apply: propext; split.
  - move=> xlub.
    split.
    + case; try by [].
      move=> ?//=.
      by apply: lub_is_ub.
    + move=> v vub.
      apply: lub_univ; eauto.
      by move=> i; apply: (vub (inr i)).
  - move=> xlub.
    split.
    + move=> i.
      rewrite (_ : A i = fam_adjoin_elt A ⊥ (inr i)); last by [].
      by apply: lub_is_ub.
    + move=> v vub.
      apply: lub_univ.
      * by apply: xlub.
      * by case.
Qed.

(* Even in a constructve setting, having predirected suprema is equivalent to being admissible.
   A priori this was a bit optimistic to expect, because it is not the case that every predirected
   subset is (constructively) either empty or directed. *)

Lemma admissible_to_has_pdlub {D : PointedPoset.type} (S : D → Prop) : admissible S → has_pdlub S.
Proof.
  move=> admS F pdirF hF x xlub.
  apply: admiss_has_dlub.
  - by apply: admS.
  - by apply: fam_adjoin_bot_directed F pdirF.
  - case.
    + by case; apply: admiss_has_bot.
    + by apply: hF.
  - by rewrite -fam_adjoin_bot_same_lub.
Qed.

Lemma has_pdlub_to_admissible {D : Poset.type} (S : D → Prop) : has_pdlub S → admissible S.
Proof.
  move=> pdlubS; split.
  - move=> x xbot.
    unshelve apply: pdlubS.
    + exists False; by [].
    + by case.
    + by case.
    + by split.
  - move=> F dirF hF x xlub.
    apply: pdlubS.
    + case: dirF=> ? pdirF.
      exact: pdirF.
    + apply: hF.
    + apply: xlub.
Qed.

Lemma scott_induction {D : Dcppo.type} (S : D → Prop) (f : map D D) :
  admissible S
  → (∀ d, S d → S (sval f d))
  → S (fix_ f).
Proof.
  move=> okS ih.
  apply: admiss_has_dlub=>//.
  - apply/pow_chain_directed/cont_mono/(svalP f).
  - elim.
    + by apply: admiss_has_bot.
    + by move=>?; apply: ih.
Qed.

Section PredFunSpace.
  Context (D : Dcpo.type) (E : Dcppo.type) (D' : D → Prop) (E' : E → Prop).

  Definition pred_fun_space : map D E → Prop :=
    λ f, ∀ x, D' x → E' (ap f x).

  Lemma pred_fun_space_has_dlub : has_dlub E' → has_dlub pred_fun_space.
  Proof.
    move=> E'dlub A dirA hA f flub x xD'.
    apply: (E'dlub (push_fam (λ g, ap g x) A)).
    - by apply: push_ap_directed.
    - by move=>?; apply: hA.
    - by apply: ap_cont2.
  Qed.

  Lemma pred_fun_space_has_bot : has_bot E' → has_bot pred_fun_space.
  Proof.
    move=> hE f fbot x hx.
    apply: hE.
    rewrite (_ : f = map_bottom)//.
    apply: bottom_is_unique=>//.
    apply: map_bottom_is_bottom.
  Qed.

  Lemma pred_fun_space_admiss : admissible E' → admissible pred_fun_space.
  Proof.
    move=> okE.
    split.
    - apply: pred_fun_space_has_bot.
      by apply: admiss_has_bot.
    - apply: pred_fun_space_has_dlub.
      by apply: admiss_has_dlub.
  Qed.
End PredFunSpace.

Section PredLift.
  Context (D : Type) (D' : D → Prop).

  Definition pred_lift : L D → Prop :=
    λ m,
    ∀ z : defd m,
      D' (m z).


  Lemma pred_lift_has_bot : has_bot pred_lift.
  Proof.
    move=> x xbot.
    rewrite (_ : x = L_bot _) //.
    apply: bottom_is_unique=>//.
    apply: L_bot_is_bot.
  Qed.

  Lemma pred_lift_has_dlub : has_dlub pred_lift.
  Proof.
    move=> A dirA hA x xlub.
    rewrite (_ : x = L_dlub _ A dirA).
    - move=> z.
      suff: (∃ i, defd (A i)).
      + case=> i Ai_defd.
        rewrite /L_dlub//=.
        rewrite <- (candidate_dlub_compute D A dirA z i Ai_defd).
        apply: hA.
      + rewrite /L_dlub//= in z.
        move: z.
        apply: Σ_lub_elim.
        * by eauto.
        * move=> //=i z.
          by exists i.
    - apply: lub_unique; eauto.
      apply: L_dlub_is_lub.
  Qed.

  Lemma pred_lift_admiss : admissible pred_lift.
  Proof.
    split.
    - apply: pred_lift_has_bot.
    - apply: pred_lift_has_dlub.
  Qed.
End PredLift.
