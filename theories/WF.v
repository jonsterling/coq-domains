From Domains Require Import Preamble Preorder Poset.

HB.mixin Record HasWf A of Preorder A :=
  {mem : A → A → Prop;
   memWf : well_founded mem;
   memLt : ∀ u v, mem u v → u ≤ v;
   memT : ∀ u v w, mem u v → mem v w → mem u w;
   memL : ∀ u v w, u ≤ v → mem v w → mem u w;
   memR : ∀ u v w, mem u v → v ≤ w → mem u w}.

HB.structure Definition WfPreorder := {A of HasWf A & Preorder A}.
HB.structure Definition WfPoset := {A of WfPreorder A & Poset A}.

Infix "≺" := mem (at level 60) : preorder_scope.

(** Let (K,k) be a pointed type and let A be a well-founded poset. Obviously A^K inherits the poset structure pointwise; I want to define a well-founded order on A^k "anchored" at k using the well-founded order on K; in other words, u ≺ v iff u k ≺ v k where k is the basepoint. *)
Module AnchoredProductOrder.
  Section AnchoredProductOrder.
    Parameter K : Type.
    Parameter k : K.
    Parameter A : WfPoset.type.

    Definition multi := K → A.

    Definition multi_lt (u v : multi) := ∀ x, u x ≤ v x.

    Lemma multi_ltR : ∀ u, multi_lt u u.
    Proof. by move=>?. Qed.

    Lemma multi_ltT : ∀ u v w, multi_lt u v → multi_lt v w → multi_lt u w.
    Proof.
      move=> u v w uv vw x.
      apply: ltT.
      - by apply: uv.
      - by apply: vw.
    Qed.

    HB.instance Definition _ := PreorderOfType.Build multi multi_lt multi_ltR multi_ltT.

    Lemma multi_ltE : ∀ u v : multi, u ≤ v → v ≤ u → u = v.
    Proof.
      move=> u v uv vu.
      apply: depfunext=> x.
        by apply: ltE.
    Qed.

    HB.instance Definition _ := PosetOfPreorder.Build multi multi_ltE.

    Definition multi_mem (u v : multi) := (u k ≺ v k) ∧ u ≤ v.

    Lemma multi_memWf : well_founded multi_mem.
    Proof.
      move=> u.
      move e : (u k) => uk.
      move: uk u e.
      apply: (well_founded_induction memWf)=> ? ih ? e.
      constructor=>?[??].
      apply: ih=>//=.
      by rewrite -e.
    Qed.

    Lemma multi_memLt : ∀ u v, multi_mem u v → u ≤ v.
    Proof. by move=>??; case. Qed.

    Lemma multi_memT : ∀ u v w, multi_mem u v → multi_mem v w → multi_mem u w.
    Proof.
      move=> u v w [uv1 uv2] [vw1 vw2]; split.
      - by apply: memT; eauto.
      - by apply: ltT; eauto.
    Qed.

    Lemma multi_memL : ∀ u v w, u ≤ v → multi_mem v w → multi_mem u w.
    Proof.
      move=> u v w uv [vw1 vw2]; split.
      - by apply: memL; eauto.
      - by apply: ltT; eauto.
    Qed.

    Lemma multi_memR : ∀ u v w, multi_mem u v → v ≤ w → multi_mem u w.
    Proof.
      move=> u v w [uv1 uv2] vw; split.
      - by apply: memR; eauto.
      - by apply: ltT; eauto.
    Qed.

    HB.instance Definition _ := HasWf.Build multi multi_mem multi_memWf multi_memLt multi_memT multi_memL multi_memR.
End AnchoredProductOrder.
