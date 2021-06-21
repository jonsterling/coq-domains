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
  - left; elim: n m H=>[|? IH] m H /=; first by [].
    by case: m H=>// ?? /=; apply/Hm/IH.
  - right; elim: m n H=>[|? IH] n H /=; first by [].
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

Theorem kleene_lfp {D : Dcppo.type} (f : map D D) :
  ∃ x, is_lub (pow_family (ap f)) x ∧ is_least_fixpoint (ap f) x.
Proof.
  case: f=>f /[dup]/cont_mono/[dup]/pow_chain_directed HD HM H /=.
  exists (dlub _ HD); split; first by apply: dlub_is_lub.
  split.
  - case: (H _ HD (dlub (pow_family f) HD)); first by auto.
    move=> H1 H2.
    apply: (lub_unique (pow_family _)); last by apply: dlub_is_lub.
    split=>/=.
    + case=>/=; [by [] | apply: H1].
    + move=>? H3; apply: H2; move=>/=i.
      by exact: (H3 (S i)).
  - move=>? H1; apply: dlub_least=>x /=.
    elim: x=>/=; first by [].
    by move=>??; rewrite -H1; apply: HM.
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
