From Coq Require Import ssrbool.
From mathcomp Require Import ssrnat.
From Domains Require Import Preamble Preorder Poset Dcpo DcpoExponential.

Set Bullet Behavior "Strict Subproofs".

(* Kleene fixed-point theorem *)

Fixpoint pow {D : PointedPoset.type} (f : D -> D) n :=
  if n is n.+1 then f (pow f n) else bottom.

Definition pow_family {D : PointedPoset.type} (f : D -> D) : Family D.
Proof. by exists nat; exact: pow f. Defined.

Lemma pow_chain {D : PointedPoset.type} (f : D -> D) n m :
  is_monotone f ->
  pow f n ≤ pow f m ∨ pow f m ≤ pow f n.
Proof.
  move=>Hm; case: (leqP n m)=>H.
  - left; elim: n m H=>[|? IH] m H //=.
    by case: m H=>// ?? /=; apply/Hm/IH.
  - right; elim: m n H=>[|? IH] n H //=.
    by case: n H=>// ?? /=; apply/Hm/IH.
Qed.

Lemma pow_chain_directed {D : PointedPoset.type} (f : D -> D) :
  is_monotone f ->
  is_directed (pow_family f).
Proof.
  move=>H; split=>/=.
  - by exists 0.
  - move=>/= n m.
    by case: (pow_chain f n m H)=>?; [exists m | exists n].
Qed.

Definition is_least_fixpoint {D : Poset.type} (f : D -> D) (x : D) :=
  f x = x ∧ ∀ y, f y = y -> x ≤ y.


Definition fix_ {D : Dcppo.type} (f : map D D) : D.
Proof.
  apply/(dlub (pow_family (sval f)))/pow_chain_directed/cont_mono.
  by case: f.
Defined.

Lemma fix_is_lub {D : Dcppo.type} (f : map D D) : is_lub (pow_family (sval f)) (fix_ f).
Proof. by apply: dlub_is_lub. Qed.

Lemma fix_is_lfp {D : Dcppo.type} (f : map D D) : is_least_fixpoint (sval f) (fix_ f).
  split.
  - case: (svalP f (pow_family (sval f)) _ (fix_ f)).
    + by apply/pow_chain_directed/cont_mono/(svalP f).
    + by [].
    + move=> H1 H2.
      apply: (lub_unique (pow_family _)); last by apply: dlub_is_lub.
      split=>/=.
      * by case=>//=; apply: H1.
      * move=>? H3; apply: H2; move=>/=i.
        by exact: (H3 (S i)).
  - move=>? H1; apply: dlub_least=> x /=.
    elim: x=>//=.
    move=>??; rewrite -H1.
    apply: cont_mono; last by [].
    by apply: svalP f.
Qed.

Opaque fix_.

Lemma fix_is_fp {D : Dcppo.type} (f : map D D) : fix_ f = sval f (fix_ f).
Proof. by case: (fix_is_lfp f)=> ->. Qed.


Theorem kleene_lfp {D : Dcppo.type} (f : map D D) :
  ∃ x, is_lub (pow_family (ap f)) x ∧ is_least_fixpoint (ap f) x.
Proof.
  exists (fix_ f); split.
  - apply: fix_is_lub.
  - apply: fix_is_lfp.
Qed.


Lemma map_pow_monotone {D : Dcppo.type} n :
  is_monotone (λ f : map D D, pow (ap f) n).
Proof.
  elim: n=>[|n IH] //=.
  move=>/= ?? l.
  apply: ltT; first by apply: l.
  by apply: cont_mono; [apply: ap_cont | apply: IH].
Qed.

Lemma map_pow_family_directed {D : Dcppo.type} {A : Family (map D D)}
  (H : is_directed A) (n : nat):
  is_directed (push_fam (λ f : map D D, pow (ap f) n) A).
Proof.
  split; first by exact: (nonempty _ H).
  move=>i j; case: (predirected _ H i j)=>/= x [??].
  by exists x; split; apply: map_pow_monotone.
Qed.



Definition closed_under_dlub {D : Dcppo.type} (S : D → Prop) :=
  ∀ (A : Family D), is_directed A → ∃ x, is_lub A x ∧ S x.

Definition admissible {D : Dcppo.type} (S : D → Prop) :=
  S ⊥ ∧ closed_under_dlub S.

Lemma fp_induction {D : Dcppo.type} (S : D → Prop) (f : map D D) :
  admissible S
  → (∀ d, S d → S (sval f d))
  → S (fix_ f).
Proof.
  move=> [botS dlubS] ih.
  case: (dlubS (pow_family (sval f))); first by apply/pow_chain_directed/cont_mono/(svalP f).
  move=> fix_f.
  move=> [fix_f_lub H].
  rewrite (_ : fix_ f = fix_f); first by [].
  apply: lub_unique; eauto.
Qed.
