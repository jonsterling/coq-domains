From Coq Require Import ssrbool.
From mathcomp Require Import ssrnat.
From Domains Require Import Preamble Preorder Poset Dcpo.

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
- left; elim: n m H=>[|? IH] m H /=; first by apply: bottom_is_bottom.
  by case: m H=>// ?? /=; apply/Hm/IH.
- right; elim: m n H=>[|? IH] n H /=; first by apply: bottom_is_bottom.
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

Theorem kleene_lfp {D : Dcppo.type} (f : D -> D) :
  is_continuous f ->
  ∃ x, is_lub (pow_family f) x ∧ is_least_fixpoint f x.
Proof.
move/[dup]/continuous_to_monotone/[dup]/pow_chain_directed=>HD HM H.
exists (dlub _ HD); split; first by apply: dlub_is_lub.
split.
- case: (H _ HD)=>H1 H2.
  apply: (lub_unique (pow_family _)); last by apply: dlub_is_lub.
  split.
  + by case=>/=; [apply: bottom_is_bottom | apply: H1].
  + move=>? H3; apply: H2=>i.
    by apply: (H3 (S i)).
- move=>? H1; apply: dlub_least=>x /=.
  elim: x=>/=; first by apply: bottom_is_bottom.
  by move=>??; rewrite -H1; apply: HM.
Qed.
