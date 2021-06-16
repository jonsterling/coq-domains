Require Import ssreflect Unicode.Utf8.
From HB Require Import structures.
Require Import Coq.Logic.Description Coq.Logic.PropExtensionality.


Set Primitive Projections.

Declare Scope preorder_scope.
Delimit Scope preorder_scope with P.

Open Scope preorder_scope.

HB.mixin Record PreorderOfType A :=
  {lt : A → A → Prop;
   ltR : ∀ x, lt x x;
   ltT : ∀ x y z, lt x y → lt y z → lt x z}.

HB.structure Definition Preorder := {A of PreorderOfType A}.

Infix "≤" := lt : preorder_scope.

HB.mixin Record PosetOfPreorder A of Preorder A :=
  {ltE : ∀ x y : A, x ≤ y → y ≤ x → x = y}.

HB.structure Definition Poset := {A of PosetOfPreorder A & Preorder A}.

Section DirectedDiagrams.
  Context {A : Poset.type} {I : Type} (d : I → A).

  Definition is_nonempty : Prop :=
    ∃ x : I, True.

  Definition is_predirected : Prop :=
    ∀ x y : I,
      ∃ z : I,
        d x ≤ d z ∧ d y ≤ d z.

  Record is_directed : Prop :=
    {nonempty : is_nonempty;
     predirected : is_predirected}.
End DirectedDiagrams.

Section Lub.
  Context {A : Poset.type} {I : Type} (d : I → A).

  Definition is_ub (x : A) :=
    ∀ z : I, d z ≤ x.

  Definition is_lub (x : A) :=
    is_ub x ∧
    ∀ z : A, is_ub z → x ≤ z.

  Lemma lub_unique : ∀ x y : A, is_lub x → is_lub y → x = y.
  Proof. move=> ? ? [? ?] [? ?]; apply: ltE; auto. Qed.
End Lub.

HB.mixin Record DcpoOfPoset D of Poset D :=
  {ltHasDirLubs : ∀ (I : Type) (A : I → D), is_directed A → ∃ x, is_lub A x}.

HB.structure Definition Dcpo := {D of DcpoOfPoset D & Poset D}.

Section DLub.
  Context {D : Dcpo.type} {I:Type} (d : I → D) (dir : is_directed d).

  Definition dlub_bundled : {x : D | is_lub d x}.
  Proof.
    apply: constructive_definite_description.
    case: (ltHasDirLubs I d dir) => //= x xlub.
    exists x; split; first by done.
    move=> y ylub.
    apply: lub_unique; by eauto.
  Qed.

  Definition dlub : D.
  Proof. case: dlub_bundled => x _; exact: x. Defined.

  Lemma dlub_is_lub : is_lub d dlub.
  Proof. rewrite /dlub; by case: dlub_bundled. Qed.

  Opaque dlub.
End DLub.


Module Σ.
  Definition Σ := Prop.
  Definition lt (x y : Σ) := x → y.
  Lemma ltR : ∀ x : Σ, x → x.
  Proof. auto. Qed.
  Lemma ltT : ∀ x y z : Σ, (x → y) → (y → z) → x → z.
  Proof. auto. Qed.

  HB.instance Definition Σ_preorder_axioms := PreorderOfType.Build Σ lt ltR ltT.

  Lemma ltE : ∀ x y : Σ, (x ≤ y) → (y ≤ x) → x = y.
  Proof. move=> *; apply: propositional_extensionality; by split. Qed.

  HB.instance Definition Σ_poset_axioms := PosetOfPreorder.Build Σ ltE.

  Lemma ltHasDLubs : ∀ (I : Type) (d : I → Σ), is_directed d → ∃ x, is_lub d x.
    move=> I d dir //=.
    exists (∃ x : I, d x).
    split; simpl.
    - rewrite /is_ub //=.
      by intuition; compute; eauto.
    - move=> z zub; move=> [? ?].
      by apply: zub; eauto.
  Qed.

End Sierpinski.
