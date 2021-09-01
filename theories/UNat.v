Require Import Lia.
From Domains Require Import Preamble Preorder Poset Dcpo.

(** The "upper naturals" *)

Definition UNat : Type :=
  {P : nat → Prop | ∀ m n : nat, m <= n → P m → P n}.

Definition UNat_defd : UNat → Prop :=
  λ x, ∃ k, sval x k.

Definition UNat_lt (M N : UNat) :=
  ∀ x, sval M x → sval N x.

Lemma UNat_ltR : ∀ x, UNat_lt x x.
Proof. by move=>?. Qed.

Lemma UNat_ltT : ∀ x y z, UNat_lt x y → UNat_lt y z → UNat_lt x z.
Proof. by move=> x y z xy yz u xu; apply/yz/xy. Qed.

HB.instance Definition UNat_preorder_axioms := PreorderOfType.Build UNat UNat_lt UNat_ltR UNat_ltT.

Lemma UNat_ltE : ∀ x y : UNat, (x ≤ y) → (y ≤ x) → x = y.
Proof.
  move=> x y xy yz.
  apply: eq_sig; last by [].
  apply: funext=> k.
  apply: propext; split.
  - apply: xy.
  - apply: yz.
Qed.

HB.instance Definition UNat_poset_axioms := PosetOfPreorder.Build UNat UNat_ltE.

Definition UNat_dsum (x : UNat) (y : ∀ u, sval x u → UNat) : UNat.
Proof.
  unshelve esplit.
  - move=> k.
    refine (∃ u v, ∃ h : sval x u, sval (y u h) v ∧ u <= k /\ v <= k).
  - abstract
      (move=> m n mn /= [u [v [hu [hv [um vm]]]]];
       exists u, v, hu; split;
       [apply: hv | lia]).
Defined.

Definition UNat_exists (I : Type) (y : I → UNat) : UNat.
Proof.
  unshelve esplit.
  - move=> k.
    refine (exists x, sval (y x) k).
  - abstract
      (by move=> m n mn /= [x hx];
          exists x; move: hx;
          move: {y} (y x) => y;
          apply: (proj2_sig y)).
Defined.

Lemma UNat_exists_is_lub : ∀ (A : Family UNat), is_lub A (UNat_exists _ A).
  move=> A; split=>/=.
  - by move=>i; move=>?; exists i.
  - move=> z zub; move=> x [i hxi].
    by apply: (zub i x).
Qed.

Lemma UNat_ltHasDLubs : ∀ (A : Family UNat), is_directed A → ∃ x, is_lub A x.
Proof.
  move=> A dir //=.
  exists (UNat_exists _ A).
  by apply: UNat_exists_is_lub.
Qed.

HB.instance Definition UNat_dcpo_axioms := DcpoOfPoset.Build UNat UNat_ltHasDLubs.

Lemma UNat_ltHasBot : ∃ x : UNat, is_bottom x.
Proof.
  unshelve esplit.
  - by exists (λ _, False).
  - by move=> ?.
Qed.

Lemma UNat_ltHasTop : ∃ x : UNat, is_top x.
Proof.
  unshelve esplit.
  - by exists (λ _, True).
  - by move=> ?.
Qed.

HB.instance Definition UNat_pointed_poset_axioms :=
  PointedPosetOfPoset.Build UNat UNat_ltHasBot.

HB.instance Definition UNat_bounded_poset_axioms :=
  BoundedPosetOfPointedPoset.Build UNat UNat_ltHasTop.
