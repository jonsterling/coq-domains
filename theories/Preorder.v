From Domains Require Import Preamble Category.

Declare Scope preorder_scope.
Delimit Scope preorder_scope with P.

Open Scope preorder_scope.
Close Scope nat_scope.

HB.mixin Record IsPreorder A :=
  {lt : A → A → Prop;
   ltR : ∀ x, lt x x;
   ltT : ∀ x y z, lt x y → lt y z → lt x z}.

HB.structure Definition Preorder := {A of IsPreorder A}.

Infix "≤" := lt : preorder_scope.

Fact ltT' {A : Preorder.type} : ∀ x y z : A, y ≤ z → x ≤ y → x ≤ z.
Proof. by move=>???/[swap]; exact: ltT. Qed.

Definition is_monotone {D E : Preorder.type} (f : D → E) :=
  ∀ x y, x ≤ y → f x ≤ f y.

Definition Preorder_hom (A B : Preorder.type) :=
  {f : A → B | is_monotone f}.

Notation "Preorder.hom" := Preorder_hom.

Check IsGraph.Build Preorder.type Preorder.hom.
HB.instance Definition _ := IsGraph.Build Preorder.type Preorder.hom.

Definition Preorder_idn (A : Preorder.type) : A ~> A.
Proof. by exists id. Defined.

Definition Preorder_seq (A B C : Preorder.type) (f : A ~> B) (g : B ~> C) : A ~> C.
Proof.
  exists (sval g \o sval f).
  abstract by move=> x y xy; rewrite/comp; apply/(svalP g)/(svalP f).
Defined.

HB.instance Definition _ := IsPrecategory.Build Preorder.type Preorder_idn Preorder_seq.

Lemma Preorder_seqL : has_seqL Preorder.type _ idn seq.
Proof. by move=> A B f; apply: eq_sig=>//=. Qed.

Lemma Preorder_seqR : has_seqR Preorder.type _ idn seq.
Proof. by move=> A B f; apply: eq_sig=>//. Qed.

Lemma Preorder_seqA : has_seqA Preorder.type _ seq.
Proof. by move=> A B C D f g h; apply: eq_sig=>//. Qed.

HB.instance Definition _ := IsCategory.Build Preorder.type Preorder_seqL Preorder_seqR Preorder_seqA.

Record ToCat (A : Preorder.type) := Encat {uncat :> A}.
Arguments uncat [A].

Local Definition hom {A} (x y : ToCat A) := uncat x ≤ uncat y.
HB.instance Definition _ A := IsGraph.Build (ToCat A) hom.

Local Definition idn {A} (x : ToCat A) : x ~> x := ltR _.
Local Definition seq {A} (x y z : ToCat A) : x ~> y → y ~> z → x ~> z := ltT _ _ _.

HB.instance Definition _ A := IsPrecategory.Build (ToCat A) idn seq.

Local Fact seqL {A} : has_seqL (ToCat A) hom idn seq.
Proof. by []. Qed.

Local Fact seqR {A} : has_seqR (ToCat A) hom idn seq.
Proof. by []. Qed.

Local Fact seqA {A} : has_seqA (ToCat A) hom seq.
Proof. by []. Qed.

HB.instance Definition _ A := IsCategory.Build (ToCat A) seqL seqR seqA.
