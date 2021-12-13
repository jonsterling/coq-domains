From Coq Require Import Arith.PeanoNat.
From Domains Require Import Preamble Preorder Poset Dcpo.

(** The "upper naturals" *)


Definition UNat : Type :=
  {P : nat → Prop | ∀ m n : nat, (m <= n)%nat → P m → P n}.

Definition UNat_defd : UNat → Prop :=
  λ x, ∃ k, sval x k.

Definition UNat_lt (M N : UNat) :=
  ∀ x, sval M x → sval N x.

Lemma UNat_ltR : ∀ x, UNat_lt x x.
Proof. by move=>?. Qed.

Lemma UNat_ltT : ∀ x y z, UNat_lt x y → UNat_lt y z → UNat_lt x z.
Proof. by move=> x y z xy yz u xu; apply/yz/xy. Qed.

HB.instance Definition UNat_preorder_axioms := IsPreorder.Build UNat UNat_lt UNat_ltR UNat_ltT.

Lemma UNat_ltE : ∀ x y : UNat, (x ≤ y) → (y ≤ x) → x = y.
Proof.
  move=>x y xy yz.
  apply: eq_sig=>//.
  apply: funext=>k.
  by apply: propext; split; [apply: xy | apply: yz].
Qed.

HB.instance Definition UNat_poset_axioms := PosetOfPreorder.Build UNat UNat_ltE.

Definition UNat_dsum (x : UNat) (y : ∀ u, sval x u → UNat) : UNat.
Proof.
  unshelve esplit.
  - move=> k.
    by exact: (∃ u v (h : sval x u), sval (y u h) v ∧ (u <= k)%nat ∧ (v <= k)%nat).
  - abstract
     (by move=> m n mn /= [u][v][hu][hv][um vm];
      exists u, v, hu; do!split=>//; apply: (Nat.le_trans _ m)).
Defined.

Definition UNat_exists (I : Type) (y : I → UNat) : UNat.
Proof.
  unshelve esplit.
  - move=> k.
    by exact: (∃ x, sval (y x) k).
  - abstract
      (by move=> m n mn /= [x hx];
       exists x; apply: (proj2_sig (y x) m)).
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

Definition UNat_bot : UNat.
Proof. by exists (λ _, False). Defined.

Lemma UNat_bot_is_bot : is_bottom UNat_bot.
Proof. by move=> ?. Qed.

Lemma UNat_ltHasBot : ∃ x : UNat, is_bottom x.
Proof. by exists UNat_bot; apply: UNat_bot_is_bot. Qed.

Lemma UNat_ltHasTop : ∃ x : UNat, is_top x.
Proof.
  by unshelve esplit; first by exists (λ _, True).
Qed.

HB.instance Definition UNat_pointed_poset_axioms :=
  PointedPosetOfPoset.Build UNat UNat_ltHasBot.

HB.instance Definition UNat_bounded_poset_axioms :=
  BoundedPosetOfPointedPoset.Build UNat UNat_ltHasTop.

Lemma UNat_lub_intro (A : Family UNat): ∀ u k ϕ, is_lub A ϕ → sval (A u) k → sval ϕ k.
Proof. by move=>????; apply: (lub_is_ub A). Qed.

Lemma UNat_lub_elim {P : UNat} {Q : nat → Prop} {A} (H : is_lub A P) : (∀ i k (z : sval (A i) k), Q k) → ∀ x (w : sval P x), Q x.
Proof.
  move=> J K.
  rewrite -(lub_unique _ _ _ (UNat_exists_is_lub _) H).
  by case=> ?; apply: J.
Qed.

Lemma UNat_bot_elim : ∀ A, ∀ z : UNat_defd ⊥, A z.
Proof.
  rewrite (_ : ⊥ = UNat_bot).
  - by apply/bottom_is_unique/UNat_bot_is_bot.
  - move=>? h.
    by exfalso; case: h.
Qed.

Lemma UNat_lub_elim_dep {P : UNat} {Q : ∀ x, sval P x → Prop} {A} (H : is_lub A P) : (∀ i k (z : sval (A i) k) w, Q k w) → ∀ x (w : sval P x), Q x w.
Proof.
  move=> J K.
  have L := eq_sym (lub_unique _ _ _ (UNat_exists_is_lub _) H).
  dependent destruction L.
  case=> ? X.
  by apply/J/X.
Qed.
