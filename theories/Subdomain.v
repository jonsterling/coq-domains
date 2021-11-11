From Coq Require Import ssrbool.
From mathcomp Require Import ssrnat.
From Domains Require Import Preamble Preorder Poset Dcpo DcpoExponential Kleene Lift Sierpinski.

Set Bullet Behavior "Strict Subproofs".


Definition has_dlub {D : Dcpo.type} (S : D → Prop) :=
  ∀ (A : Family D), is_directed A → (∀ x, S (A x)) → ∀ x, is_lub A x → S x.

Definition has_bot {D : Dcpo.type} (S : D → Prop) :=
  ∀ x, is_bottom x → S x.

Definition admissible {D : Dcppo.type} (S : D → Prop) :=
  has_bot S ∧ has_dlub S.

Lemma admiss_has_bot {D : Dcppo.type} (S : D → Prop) : admissible S → has_bot S.
Proof. by case. Qed.

Lemma admiss_has_dlub {D : Dcppo.type} (S : D → Prop) : admissible S → has_dlub S.
Proof. by case. Qed.

Lemma fp_induction {D : Dcppo.type} (S : D → Prop) (f : map D D) :
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