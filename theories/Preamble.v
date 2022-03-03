Require Export ssreflect ssrfun Unicode.Utf8.
From HB Require Export structures.
Require Export Coq.Logic.Description Coq.Logic.PropExtensionality Coq.Logic.FunctionalExtensionality Program.Equality.
Export EqNotations.

Set Primitive Projections.

Definition iota {X : Type} (P : X → Prop) (h : exists! x, P x) : X :=
  proj1_sig (constructive_definite_description _ h).

Lemma iota_prop {X : Type} (P : X → Prop) (h : exists! x, P x) : P (iota P h).
Proof. rewrite /iota; apply proj2_sig. Qed.

Arguments proj1_sig {A P}.
Notation sval := proj1_sig.

Scheme eq_ind := Induction for eq Sort Type.
Arguments eq_ind [A] x P f y e.

Definition extract {X : Type} {P : X → Prop} : (∀ x y, P x → P y → x = y) → (∃ x, P x) → X.
Proof.
  move=> H J.
  apply: (@iota X P).
  case: J=> x xP.
  exists x; split=>//.
  by move=>?; apply: H.
Defined.

Definition extract_prop {X : Type} {P : X → Prop} : ∀ H J, P (@extract X P H J).
Proof.
  move=> ? ?.
  apply: iota_prop.
Qed.

Opaque extract.

Module Im.
  Section Im.
    Context {X Y : Type} (f : X → Y).

    Definition T : Type :=
      { y : Y | ∃ x, f x = y }.

    Definition surj : X → T.
    Proof. by move=> x; exists (f x); exists x. Defined.

    Definition inj : T → Y.
    Proof. by apply: proj1_sig. Defined.

    Lemma inj_injective : ∀ x y, inj x = inj y → x = y.
    Proof. by move=> x y h; apply/eq_sig/proof_irrelevance. Qed.

    Lemma surj_surjective : ∀ i : T, ∃ x : X, surj x = i.
    Proof. by move=> [y [x h]]; exists x; apply/eq_sig/proof_irrelevance. Qed.
  End Im.
End Im.

Notation Im := Im.T.

Notation propext := propositional_extensionality.
Notation funext := functional_extensionality.
Notation depfunext := functional_extensionality_dep.
Notation proofirr := proof_irrelevance.

#[global]
Hint Resolve proofirr : core.


Definition surjective {E B} (f : E → B) : Prop :=
  ∀ x : B, ∃ y : E, f y = x.

Definition is_isomorphism {A B} (f : A → B) : Prop :=
  ∀ x : B, exists! y : A, f y = x.

Lemma balanced {A B} (f : A → B) : injective f → surjective f → is_isomorphism f.
Proof.
  move=> inj surj b.
  case: (surj b)=> a ha.
  exists a; split=>//=.
  move=> a' ha'.
  apply: inj.
  by congruence.
Qed.

Lemma iso_injective {A B} (f : A → B) : is_isomorphism f → injective f.
Proof.
  move=> iso a a' h.
  case: (iso (f a)) (iso (f a'))=> [za [hza1 /(_ a') hza2]] [za' [hza'1 hza'2]].
  by move: (hza'2 za) (hza'2 a); rewrite hza2//=; move=> <-//= <-//=; congruence.
Qed.

Lemma iso_surjective {A B} (f : A → B) : is_isomorphism f → surjective f.
Proof. by move=> iso b; case: (iso b) => a [? _]; exists a. Qed.




Module Coeq.
  Private Inductive T {A B} (f g : A → B) :=
  | intro : B → T f g.

  Arguments intro [A] [B] [f] [g] x.

  Section Operations.
    Context {A B} {f g : A → B}.

    Axiom glue : ∀ {x}, @intro A B f g (f x) = @intro A B f g (g x).

    Definition rec {C} (h : B → C) : (h \o f = h \o g) → T f g → C.
    Proof. by move=> ?; case. Defined.

    Definition ind (C : T f g → Type) (h : ∀ b, C (intro b)) : (∀ x, rew [C] glue in h (f x) = h (g x)) → ∀ x : T f g, C x.
    Proof. by move=> ?; case. Defined.

  End Operations.
End Coeq.

Module Quotient.
  Definition gph A (R : A → A → Prop) := {p : A * A | R p.1 p.2}.

  Definition pi1 {A} (R : A → A → Prop) : gph A R → A.
  Proof. by move/proj1_sig/fst. Defined.

  Definition pi2 {A} (R : A → A → Prop) : gph A R → A.
  Proof. by move/proj1_sig/snd. Defined.

  Definition T A (R : A → A → Prop) := Coeq.T (pi1 R) (pi2 R).

  Section Operations.
    Context {A} {R : A → A → Prop}.

    Definition intro : A → T A R.
    Proof. apply: Coeq.intro. Defined.

    Definition rec {C} (h : A → C) : (∀ x y : A, R x y → h x = h y) → T A R → C.
    Proof.
      move=> H.
      apply: (Coeq.rec h).
      abstract by apply: funext; case=> ? ?; rewrite /pi1 /pi2 //=; apply: H.
    Defined.

    Definition glue : ∀ {x y}, R x y → intro x = intro y.
    Proof.
      move=> x y h.
      rewrite /intro.
      pose xyh : gph A R := exist _ (x,y) h.
      rewrite (_ : x = pi1 _ xyh); first by [].
      rewrite (_ : y = pi2 _ xyh) ; first by [].
      apply Coeq.glue.
    Qed.

    Definition ind (C : T A R → Type) (h : ∀ x : A, C (intro x)) : (∀ (x y : A) (xy : R x y), rew [C] glue xy in h x = h y) → ∀ x : T A R, C x.
    Proof.
      move=> H.
      apply: (Coeq.ind C h); case; case=> x y xy.
      abstract by rewrite /pi1 /pi2 //= -(H x y xy); congr eq_rect.
    Defined.



    Definition indp (C : T A R → Prop) (h : ∀ x : A, C (intro x)) : ∀ x : T A R, C x.
    Proof. by apply: ind. Qed.

    Definition ind_eta (C : T A R → Type) (f1 f2 : ∀ x : T A R, C x) : (∀ x, f1 (intro x) = f2 (intro x)) → f1 = f2.
    Proof. by move=>?; apply: depfunext; apply: indp. Qed.


    Section Effectivity.
      Context `{RelationClasses.Equivalence A R}.

      Local Definition R' : T A R → A → Prop.
      Proof.
        apply: (rec R)=> x y xy.
        apply: funext=> z.
        apply: propext; split.
        - move=> ?.
          transitivity x=>//.
          by symmetry.
        - move=> ?.
          by transitivity y=>//.
      Defined.

      Definition eff {x y : A} : intro x = intro y → R x y.
      Proof.
        move=> h.
        symmetry.
        rewrite (_ : R y x = R x x); last by reflexivity.
        by move: (f_equal R' h) => //= ->.
      Qed.

      Definition glue_is_iso {x y : A} : is_isomorphism (@glue x y).
      Proof.
        move=> e.
        unshelve esplit=>//.
        by apply: eff.
      Qed.
    End Effectivity.
  End Operations.
End Quotient.
