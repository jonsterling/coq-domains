
HIERARCHY BUILDER PATCH v1
File "./theories/Category.v", line 9, column 78, characters 156-234:
Module IsGraph.
Section IsGraph.
Variable obj : Type.
Local Arguments obj : clear implicits.
Section axioms_.
Local Unset Implicit Arguments.
Record axioms_ (obj : Type) : Type := Axioms_
  { hom : forall (_ : obj) (_ : obj), Type; }.
End axioms_.

Global Arguments axioms_ : clear implicits.
Global Arguments Axioms_ : clear implicits.
Global Arguments hom : clear implicits.
End IsGraph.
Global Arguments axioms_ : clear implicits.
Global Arguments Axioms_ : clear implicits.
Definition phant_Build : forall (obj : Type)
                           (_ : forall (_ : obj) (_ : obj), Type), axioms_ obj :=
  fun (obj : Type) (hom : forall (_ : obj) (_ : obj), Type) => Axioms_ obj hom.
Local Arguments phant_Build : clear implicits.
Notation Build X1 := ( phant_Build X1).
Definition phant_axioms : forall _ : Type, Type :=
  fun obj : Type => axioms_ obj.
Local Arguments phant_axioms : clear implicits.
Notation axioms X1 := ( phant_axioms X1).
Definition identity_builder : forall (obj : Type) (_ : axioms_ obj),
                              axioms_ obj :=
  fun (obj : Type) (x : axioms_ obj) => x.
Local Arguments identity_builder : clear implicits.
Module Exports.
Global Arguments Axioms_ {_}.
End Exports.
End IsGraph.
Export IsGraph.Exports.
Notation IsGraph X1 := ( IsGraph.phant_axioms X1).
HIERARCHY BUILDER PATCH v1
File "./theories/Category.v", line 13, column 63, characters 236-299:
Module Graph.
Section axioms_.
Local Unset Implicit Arguments.
Record axioms_ (𝒞 : Type) : Type := Class
  { Category_IsGraph_mixin : IsGraph.axioms_ 𝒞; }.
End axioms_.

Global Arguments axioms_ : clear implicits.
Global Arguments Class : clear implicits.
Global Arguments Category_IsGraph_mixin : clear implicits.
Section type.
Local Unset Implicit Arguments.
Record type  : Type := Pack { sort : Type; class : axioms_ sort; }.
End type.

Global Arguments type : clear implicits.
Global Arguments Pack : clear implicits.
Global Arguments sort : clear implicits.
Global Arguments class : clear implicits.
Definition phant_clone : forall (𝒞 : Type) (cT : type) (c : axioms_ 𝒞)
                           (_ : unify Type Type 𝒞 (sort cT) nomsg)
                           (_ : unify type type cT (Pack 𝒞 c) nomsg), type :=
  fun (𝒞 : Type) (cT : type) (c : axioms_ 𝒞)
    (_ : unify Type Type 𝒞 (sort cT) nomsg)
    (_ : unify type type cT (Pack 𝒞 c) nomsg) => Pack 𝒞 c.
Local Arguments phant_clone : clear implicits.
Notation clone X2 X1 := ( phant_clone X2 X1 _ (@id_phant _ _) (@id_phant _ _)).
Definition pack_ :=
  fun (𝒞 : Type) (m : IsGraph.axioms_ 𝒞) => Pack 𝒞 (Class 𝒞 m).
Local Arguments pack_ : clear implicits.
Module Exports.
Coercion sort : Category.Graph.type >-> Sortclass.
Coercion Category_IsGraph_mixin : Category.Graph.axioms_ >-> Category.IsGraph.axioms_.
End Exports.
Import Exports.
Definition phant_on_ : forall (𝒞 : type) (_ : phant (sort 𝒞)), axioms_ (sort 𝒞) :=
  fun (𝒞 : type) (_ : phant (sort 𝒞)) => class 𝒞.
Local Arguments phant_on_ : clear implicits.
Notation on_ X1 := ( phant_on_ _ (Phant X1)).
Notation copy X2 X1 := ( phant_on_ _ (Phant X1) : axioms_ X2).
Notation on X1 := ( phant_on_ _ (Phant _) : axioms_ X1).
Module EtaAndMixinExports.
Section hb_instance_1.
Variable 𝒞 : type.
Local Arguments 𝒞 : clear implicits.
Definition HB_unnamed_factory_2 : axioms_ (@eta Type (sort 𝒞)) := class 𝒞.
Local Arguments HB_unnamed_factory_2 : clear implicits.
Definition Category_Graph__to__Category_IsGraph : IsGraph.axioms_
                                                    (@eta Type (sort 𝒞)) :=
  Category_IsGraph_mixin (@eta Type (sort 𝒞)) HB_unnamed_factory_2.
Local Arguments Category_Graph__to__Category_IsGraph : clear implicits.
Definition HB_unnamed_mixin_4 :=
  Category_IsGraph_mixin (@eta Type (sort 𝒞)) HB_unnamed_factory_2.
Local Arguments HB_unnamed_mixin_4 : clear implicits.
Definition structures_eta__canonical__Category_Graph : type :=
  Pack (@eta Type (sort 𝒞)) (Class (@eta Type (sort 𝒞)) HB_unnamed_mixin_4).
Local Arguments structures_eta__canonical__Category_Graph : clear implicits.
Global Canonical structures_eta__canonical__Category_Graph.
End hb_instance_1.
End EtaAndMixinExports.
End Graph.
Export Graph.Exports.
Export Graph.EtaAndMixinExports.
Definition hom : forall (s : Graph.type) (_ : Graph.sort s) (_ : Graph.sort s),
                 Type :=
  fun (s : Graph.type) (H H0 : Graph.sort s) =>
  IsGraph.hom (Graph.sort s)
    (Graph.Category_IsGraph_mixin (Graph.sort s) (Graph.class s)) H H0.
Local Arguments hom : clear implicits.
Global Arguments hom {_}.
Module ElpiOperations5.
End ElpiOperations5.
Export ElpiOperations5.
Notation Graph X1 := ( Graph.axioms_ X1).
HIERARCHY BUILDER PATCH v1
File "./theories/Category.v", line 18, column 149, characters 335-484:
Module IsPrecategory.
Section IsPrecategory.
Variable 𝒞 : Type.
Local Arguments 𝒞 : clear implicits.
Variable local_mixin_Category_IsGraph : IsGraph.axioms_ 𝒞.
Local Arguments local_mixin_Category_IsGraph : clear implicits.
Definition IsPrecategory_𝒞__canonical__Category_Graph : Graph.type :=
  Graph.Pack 𝒞 (Graph.Class 𝒞 local_mixin_Category_IsGraph).
Local Arguments IsPrecategory_𝒞__canonical__Category_Graph : clear implicits.
Local Canonical IsPrecategory_𝒞__canonical__Category_Graph.
Section axioms_.
Local Unset Implicit Arguments.
Record axioms_
    (𝒞 : Type)(local_mixin_Category_IsGraph : IsGraph.axioms_ 𝒞) : Type
  := Axioms_
  {
    idn : forall x : 𝒞,
          @hom (Graph.Pack 𝒞 (Graph.Class 𝒞 local_mixin_Category_IsGraph)) x x;
    seq : forall (x y z : 𝒞)
            (_ : @hom
                   (Graph.Pack 𝒞 (Graph.Class 𝒞 local_mixin_Category_IsGraph))
                   x y)
            (_ : @hom
                   (Graph.Pack 𝒞 (Graph.Class 𝒞 local_mixin_Category_IsGraph))
                   y z),
          @hom (Graph.Pack 𝒞 (Graph.Class 𝒞 local_mixin_Category_IsGraph)) x z;
    }.
End axioms_.

Global Arguments axioms_ : clear implicits.
Global Arguments Axioms_ : clear implicits.
Global Arguments idn : clear implicits.
Global Arguments seq : clear implicits.
End IsPrecategory.
Global Arguments axioms_ : clear implicits.
Global Arguments Axioms_ : clear implicits.
Definition phant_Build : forall (𝒞 : Type) (m : IsGraph.axioms_ 𝒞)
                           (𝒞local : Type) (_ : unify Type Type 𝒞local 𝒞 nomsg)
                           (s : Graph.type)
                           (_ : unify Type Type 𝒞local (Graph.sort s)
                                  (is_not_canonically_a Graph.type))
                           (c : Graph.axioms_ 𝒞local)
                           (_ : unify Graph.type Graph.type s
                                  (Graph.Pack 𝒞local c) nomsg)
                           (m0 : IsGraph.axioms_ 𝒞local)
                           (_ : unify (IsGraph.axioms_ 𝒞local)
                                  (IsGraph.axioms_ 𝒞) m0 m nomsg)
                           (_ : unify (Graph.axioms_ 𝒞local)
                                  (Graph.axioms_ 𝒞local)
                                  (Graph.Class 𝒞local m0) c nomsg)
                           (_ : forall x : 𝒞,
                                @hom (Graph.Pack 𝒞 (Graph.Class 𝒞 m)) x x)
                           (_ : forall (x y z : 𝒞)
                                  (_ : @hom (Graph.Pack 𝒞 (Graph.Class 𝒞 m)) x
                                         y)
                                  (_ : @hom (Graph.Pack 𝒞 (Graph.Class 𝒞 m)) y
                                         z),
                                @hom (Graph.Pack 𝒞 (Graph.Class 𝒞 m)) x z),
                         axioms_ 𝒞 m :=
  fun (𝒞 : Type) (m : IsGraph.axioms_ 𝒞) (𝒞local : Type)
    (_ : unify Type Type 𝒞local 𝒞 nomsg) (s : Graph.type)
    (_ : unify Type Type 𝒞local (Graph.sort s)
           (is_not_canonically_a Graph.type)) (c : Graph.axioms_ 𝒞local)
    (_ : unify Graph.type Graph.type s (Graph.Pack 𝒞local c) nomsg)
    (m0 : IsGraph.axioms_ 𝒞local)
    (_ : unify (IsGraph.axioms_ 𝒞local) (IsGraph.axioms_ 𝒞) m0 m nomsg)
    (_ : unify (Graph.axioms_ 𝒞local) (Graph.axioms_ 𝒞local)
           (Graph.Class 𝒞local m0) c nomsg)
    (idn : forall x : 𝒞, @hom (Graph.Pack 𝒞 (Graph.Class 𝒞 m)) x x)
    (seq : forall (x y z : 𝒞) (_ : @hom (Graph.Pack 𝒞 (Graph.Class 𝒞 m)) x y)
             (_ : @hom (Graph.Pack 𝒞 (Graph.Class 𝒞 m)) y z),
           @hom (Graph.Pack 𝒞 (Graph.Class 𝒞 m)) x z) => Axioms_ 𝒞 m idn seq.
Local Arguments phant_Build : clear implicits.
Notation Build X1 := (
  phant_Build X1 _ _ (@id_phant _ _) _ (@id_phant _ _) _ (@id_phant _ _) _
    (@id_phant _ _) (@id_phant _ _)).
Definition phant_axioms : forall (𝒞 : Type) (m : IsGraph.axioms_ 𝒞)
                            (𝒞local : Type)
                            (_ : unify Type Type 𝒞local 𝒞 nomsg)
                            (s : Graph.type)
                            (_ : unify Type Type 𝒞local (Graph.sort s)
                                   (is_not_canonically_a Graph.type))
                            (c : Graph.axioms_ 𝒞local)
                            (_ : unify Graph.type Graph.type s
                                   (Graph.Pack 𝒞local c) nomsg)
                            (m0 : IsGraph.axioms_ 𝒞local)
                            (_ : unify (IsGraph.axioms_ 𝒞local)
                                   (IsGraph.axioms_ 𝒞) m0 m nomsg)
                            (_ : unify (Graph.axioms_ 𝒞local)
                                   (Graph.axioms_ 𝒞local)
                                   (Graph.Class 𝒞local m0) c nomsg), Type :=
  fun (𝒞 : Type) (m : IsGraph.axioms_ 𝒞) (𝒞local : Type)
    (_ : unify Type Type 𝒞local 𝒞 nomsg) (s : Graph.type)
    (_ : unify Type Type 𝒞local (Graph.sort s)
           (is_not_canonically_a Graph.type)) (c : Graph.axioms_ 𝒞local)
    (_ : unify Graph.type Graph.type s (Graph.Pack 𝒞local c) nomsg)
    (m0 : IsGraph.axioms_ 𝒞local)
    (_ : unify (IsGraph.axioms_ 𝒞local) (IsGraph.axioms_ 𝒞) m0 m nomsg)
    (_ : unify (Graph.axioms_ 𝒞local) (Graph.axioms_ 𝒞local)
           (Graph.Class 𝒞local m0) c nomsg) => axioms_ 𝒞 m.
Local Arguments phant_axioms : clear implicits.
Notation axioms X1 := (
  phant_axioms X1 _ _ (@id_phant _ _) _ (@id_phant _ _) _ (@id_phant _ _) _
    (@id_phant _ _) (@id_phant _ _)).
Definition identity_builder : forall (𝒞 : Type) (m : IsGraph.axioms_ 𝒞)
                                (_ : axioms_ 𝒞 m), axioms_ 𝒞 m :=
  fun (𝒞 : Type) (m : IsGraph.axioms_ 𝒞) (x : axioms_ 𝒞 m) => x.
Local Arguments identity_builder : clear implicits.
Module Exports.
Global Arguments Axioms_ {_} {_}.
End Exports.
End IsPrecategory.
Export IsPrecategory.Exports.
Notation IsPrecategory X1 := (
  IsPrecategory.phant_axioms X1 _ _ (@id_phant _ _) _ (@id_phant _ _) _
    (@id_phant _ _) _ (@id_phant _ _) (@id_phant _ _)).
HIERARCHY BUILDER PATCH v1
File "./theories/Category.v", line 23, column 83, characters 486-569:
Module Precategory.
Section axioms_.
Local Unset Implicit Arguments.
Record axioms_ (𝒞 : Type) : Type := Class
  {
    Category_IsGraph_mixin : IsGraph.axioms_ 𝒞;
    Category_IsPrecategory_mixin : IsPrecategory.axioms_ 𝒞
                                     Category_IsGraph_mixin;
    }.
End axioms_.

Global Arguments axioms_ : clear implicits.
Global Arguments Class : clear implicits.
Global Arguments Category_IsGraph_mixin : clear implicits.
Global Arguments Category_IsPrecategory_mixin : clear implicits.
Section type.
Local Unset Implicit Arguments.
Record type  : Type := Pack { sort : Type; class : axioms_ sort; }.
End type.

Global Arguments type : clear implicits.
Global Arguments Pack : clear implicits.
Global Arguments sort : clear implicits.
Global Arguments class : clear implicits.
Definition phant_clone : forall (𝒞 : Type) (cT : type) (c : axioms_ 𝒞)
                           (_ : unify Type Type 𝒞 (sort cT) nomsg)
                           (_ : unify type type cT (Pack 𝒞 c) nomsg), type :=
  fun (𝒞 : Type) (cT : type) (c : axioms_ 𝒞)
    (_ : unify Type Type 𝒞 (sort cT) nomsg)
    (_ : unify type type cT (Pack 𝒞 c) nomsg) => Pack 𝒞 c.
Local Arguments phant_clone : clear implicits.
Notation clone X2 X1 := ( phant_clone X2 X1 _ (@id_phant _ _) (@id_phant _ _)).
Definition pack_ :=
  fun (𝒞 : Type) (m : IsGraph.axioms_ 𝒞) (m0 : IsPrecategory.axioms_ 𝒞 m) =>
  Pack 𝒞 (Class 𝒞 m m0).
Local Arguments pack_ : clear implicits.
Module Exports.
Coercion sort : Category.Precategory.type >-> Sortclass.
Definition Category_Precategory_class__to__Category_Graph_class : forall
                                                                    (𝒞 : Type)
                                                                    (_ : 
                                                                    axioms_ 𝒞),
                                                                  Graph.axioms_
                                                                    𝒞 :=
  fun (𝒞 : Type) (c : axioms_ 𝒞) => Graph.Class 𝒞 (Category_IsGraph_mixin 𝒞 c).
Local Arguments Category_Precategory_class__to__Category_Graph_class : clear implicits.
Coercion Category_Precategory_class__to__Category_Graph_class : Category.Precategory.axioms_ >-> Category.Graph.axioms_.
Definition Category_Precategory__to__Category_Graph : forall _ : type,
                                                      Graph.type :=
  fun s : type =>
  Graph.Pack (sort s)
    (Category_Precategory_class__to__Category_Graph_class (sort s) (class s)).
Local Arguments Category_Precategory__to__Category_Graph : clear implicits.
Coercion Category_Precategory__to__Category_Graph : Category.Precategory.type >-> Category.Graph.type.
Global Canonical Category_Precategory__to__Category_Graph.
Coercion Category_IsGraph_mixin : Category.Precategory.axioms_ >-> Category.IsGraph.axioms_.
Coercion Category_IsPrecategory_mixin : Category.Precategory.axioms_ >-> Category.IsPrecategory.axioms_.
End Exports.
Import Exports.
Definition phant_on_ : forall (𝒞 : type) (_ : phant (sort 𝒞)), axioms_ (sort 𝒞) :=
  fun (𝒞 : type) (_ : phant (sort 𝒞)) => class 𝒞.
Local Arguments phant_on_ : clear implicits.
Notation on_ X1 := ( phant_on_ _ (Phant X1)).
Notation copy X2 X1 := ( phant_on_ _ (Phant X1) : axioms_ X2).
Notation on X1 := ( phant_on_ _ (Phant _) : axioms_ X1).
Module EtaAndMixinExports.
Section hb_instance_6.
Variable 𝒞 : type.
Local Arguments 𝒞 : clear implicits.
Definition HB_unnamed_factory_7 : axioms_ (@eta Type (sort 𝒞)) := class 𝒞.
Local Arguments HB_unnamed_factory_7 : clear implicits.
Definition Category_Precategory__to__Category_IsGraph : IsGraph.axioms_
                                                          (@eta Type
                                                             (Graph.sort
                                                                (Category_Precategory__to__Category_Graph
                                                                   𝒞))) :=
  HB_unnamed_mixin_4 (Category_Precategory__to__Category_Graph 𝒞).
Local Arguments Category_Precategory__to__Category_IsGraph : clear implicits.
Definition Category_Precategory__to__Category_IsPrecategory : IsPrecategory.axioms_
                                                                (@eta Type
                                                                   (sort 𝒞))
                                                                (Category_IsGraph_mixin
                                                                   (@eta Type
                                                                    (sort 𝒞))
                                                                   HB_unnamed_factory_7) :=
  Category_IsPrecategory_mixin (@eta Type (sort 𝒞)) HB_unnamed_factory_7.
Local Arguments Category_Precategory__to__Category_IsPrecategory : clear implicits.
Definition HB_unnamed_mixin_10 :=
  Category_IsPrecategory_mixin (@eta Type (sort 𝒞)) HB_unnamed_factory_7.
Local Arguments HB_unnamed_mixin_10 : clear implicits.
Definition structures_eta__canonical__Category_Precategory : type :=
  Pack (@eta Type (sort 𝒞))
    (Class (@eta Type (sort 𝒞))
       (HB_unnamed_mixin_4 (Category_Precategory__to__Category_Graph 𝒞))
       HB_unnamed_mixin_10).
Local Arguments structures_eta__canonical__Category_Precategory : clear implicits.
Global Canonical structures_eta__canonical__Category_Precategory.
End hb_instance_6.
End EtaAndMixinExports.
End Precategory.
Export Precategory.Exports.
Export Precategory.EtaAndMixinExports.
Definition idn : forall (s : Precategory.type) (x : Precategory.sort s),
                 @hom
                   (Graph.Pack (Precategory.sort s)
                      (Graph.Class (Precategory.sort s)
                         (Precategory.Category_IsGraph_mixin
                            (Precategory.sort s) (Precategory.class s)))) x x :=
  fun (s : Precategory.type) (x : Precategory.sort s) =>
  IsPrecategory.idn (Precategory.sort s)
    (Precategory.Category_IsGraph_mixin (Precategory.sort s)
       (Precategory.class s))
    (Precategory.Category_IsPrecategory_mixin (Precategory.sort s)
       (Precategory.class s)) x.
Local Arguments idn : clear implicits.
Global Arguments idn {_}.
Definition seq : forall (s : Precategory.type) (x y z : Precategory.sort s)
                   (_ : @hom
                          (Graph.Pack (Precategory.sort s)
                             (Graph.Class (Precategory.sort s)
                                (Precategory.Category_IsGraph_mixin
                                   (Precategory.sort s) (Precategory.class s))))
                          x y)
                   (_ : @hom
                          (Graph.Pack (Precategory.sort s)
                             (Graph.Class (Precategory.sort s)
                                (Precategory.Category_IsGraph_mixin
                                   (Precategory.sort s) (Precategory.class s))))
                          y z),
                 @hom
                   (Graph.Pack (Precategory.sort s)
                      (Graph.Class (Precategory.sort s)
                         (Precategory.Category_IsGraph_mixin
                            (Precategory.sort s) (Precategory.class s)))) x z :=
  fun (s : Precategory.type) (x y z : Precategory.sort s)
    (H : @hom
           (Graph.Pack (Precategory.sort s)
              (Graph.Class (Precategory.sort s)
                 (Precategory.Category_IsGraph_mixin (Precategory.sort s)
                    (Precategory.class s)))) x y)
    (H0 : @hom
            (Graph.Pack (Precategory.sort s)
               (Graph.Class (Precategory.sort s)
                  (Precategory.Category_IsGraph_mixin (Precategory.sort s)
                     (Precategory.class s)))) y z) =>
  IsPrecategory.seq (Precategory.sort s)
    (Precategory.Category_IsGraph_mixin (Precategory.sort s)
       (Precategory.class s))
    (Precategory.Category_IsPrecategory_mixin (Precategory.sort s)
       (Precategory.class s)) x y z H H0.
Local Arguments seq : clear implicits.
Global Arguments seq {_}.
Module ElpiOperations11.
End ElpiOperations11.
Export ElpiOperations11.
Notation Precategory X1 := ( Precategory.axioms_ X1).
HIERARCHY BUILDER PATCH v1
File "./theories/Category.v", line 36, column 162, characters 1114-1276:
Module IsCategory.
Section IsCategory.
Variable 𝒞 : Type.
Local Arguments 𝒞 : clear implicits.
Variable local_mixin_Category_IsGraph : IsGraph.axioms_ 𝒞.
Local Arguments local_mixin_Category_IsGraph : clear implicits.
Variable local_mixin_Category_IsPrecategory :
  IsPrecategory.axioms_ 𝒞 local_mixin_Category_IsGraph.
Local Arguments local_mixin_Category_IsPrecategory : clear implicits.
Definition IsCategory_𝒞__canonical__Category_Graph : Graph.type :=
  Graph.Pack 𝒞 (Graph.Class 𝒞 local_mixin_Category_IsGraph).
Local Arguments IsCategory_𝒞__canonical__Category_Graph : clear implicits.
Local Canonical IsCategory_𝒞__canonical__Category_Graph.
Definition IsCategory_𝒞__canonical__Category_Precategory : Precategory.type :=
  Precategory.Pack 𝒞
    (Precategory.Class 𝒞 local_mixin_Category_IsGraph
       local_mixin_Category_IsPrecategory).
Local Arguments IsCategory_𝒞__canonical__Category_Precategory : clear implicits.
Local Canonical IsCategory_𝒞__canonical__Category_Precategory.
Section axioms_.
Local Unset Implicit Arguments.
Record axioms_
    (𝒞 : Type)(local_mixin_Category_IsGraph : IsGraph.axioms_ 𝒞)(local_mixin_Category_IsPrecategory : 
                                                                  IsPrecategory.axioms_
                                                                    𝒞
                                                                    local_mixin_Category_IsGraph) : Type
  := Axioms_
  {
    seqL : has_seqL 𝒞
             (@hom (Graph.Pack 𝒞 (Graph.Class 𝒞 local_mixin_Category_IsGraph)))
             (@idn
                (Precategory.Pack 𝒞
                   (Precategory.Class 𝒞 local_mixin_Category_IsGraph
                      local_mixin_Category_IsPrecategory)))
             (@seq
                (Precategory.Pack 𝒞
                   (Precategory.Class 𝒞 local_mixin_Category_IsGraph
                      local_mixin_Category_IsPrecategory)));
    seqR : has_seqR 𝒞
             (@hom (Graph.Pack 𝒞 (Graph.Class 𝒞 local_mixin_Category_IsGraph)))
             (@idn
                (Precategory.Pack 𝒞
                   (Precategory.Class 𝒞 local_mixin_Category_IsGraph
                      local_mixin_Category_IsPrecategory)))
             (@seq
                (Precategory.Pack 𝒞
                   (Precategory.Class 𝒞 local_mixin_Category_IsGraph
                      local_mixin_Category_IsPrecategory)));
    seqA : has_seqA 𝒞
             (@hom (Graph.Pack 𝒞 (Graph.Class 𝒞 local_mixin_Category_IsGraph)))
             (@seq
                (Precategory.Pack 𝒞
                   (Precategory.Class 𝒞 local_mixin_Category_IsGraph
                      local_mixin_Category_IsPrecategory)));
    }.
End axioms_.

Global Arguments axioms_ : clear implicits.
Global Arguments Axioms_ : clear implicits.
Global Arguments seqL : clear implicits.
Global Arguments seqR : clear implicits.
Global Arguments seqA : clear implicits.
End IsCategory.
Global Arguments axioms_ : clear implicits.
Global Arguments Axioms_ : clear implicits.
Definition phant_Build : forall (𝒞 : Type) (m : IsGraph.axioms_ 𝒞)
                           (m0 : IsPrecategory.axioms_ 𝒞 m) (𝒞local : Type)
                           (_ : unify Type Type 𝒞local 𝒞 nomsg)
                           (s : Precategory.type)
                           (_ : unify Type Type 𝒞local (Precategory.sort s)
                                  (is_not_canonically_a Precategory.type))
                           (c : Precategory.axioms_ 𝒞local)
                           (_ : unify Precategory.type Precategory.type s
                                  (Precategory.Pack 𝒞local c) nomsg)
                           (m1 : IsGraph.axioms_ 𝒞local)
                           (_ : unify (IsGraph.axioms_ 𝒞local)
                                  (IsGraph.axioms_ 𝒞) m1 m nomsg)
                           (m2 : IsPrecategory.axioms_ 𝒞local m1)
                           (_ : unify (IsPrecategory.axioms_ 𝒞local m1)
                                  (IsPrecategory.axioms_ 𝒞 m) m2 m0 nomsg)
                           (_ : unify (Precategory.axioms_ 𝒞local)
                                  (Precategory.axioms_ 𝒞local)
                                  (Precategory.Class 𝒞local m1 m2) c nomsg)
                           (_ : has_seqL 𝒞
                                  (@hom (Graph.Pack 𝒞 (Graph.Class 𝒞 m)))
                                  (@idn
                                     (Precategory.Pack 𝒞
                                        (Precategory.Class 𝒞 m m0)))
                                  (@seq
                                     (Precategory.Pack 𝒞
                                        (Precategory.Class 𝒞 m m0))))
                           (_ : has_seqR 𝒞
                                  (@hom (Graph.Pack 𝒞 (Graph.Class 𝒞 m)))
                                  (@idn
                                     (Precategory.Pack 𝒞
                                        (Precategory.Class 𝒞 m m0)))
                                  (@seq
                                     (Precategory.Pack 𝒞
                                        (Precategory.Class 𝒞 m m0))))
                           (_ : has_seqA 𝒞
                                  (@hom (Graph.Pack 𝒞 (Graph.Class 𝒞 m)))
                                  (@seq
                                     (Precategory.Pack 𝒞
                                        (Precategory.Class 𝒞 m m0)))),
                         axioms_ 𝒞 m m0 :=
  fun (𝒞 : Type) (m : IsGraph.axioms_ 𝒞) (m0 : IsPrecategory.axioms_ 𝒞 m)
    (𝒞local : Type) (_ : unify Type Type 𝒞local 𝒞 nomsg) (s : Precategory.type)
    (_ : unify Type Type 𝒞local (Precategory.sort s)
           (is_not_canonically_a Precategory.type))
    (c : Precategory.axioms_ 𝒞local)
    (_ : unify Precategory.type Precategory.type s (Precategory.Pack 𝒞local c)
           nomsg) (m1 : IsGraph.axioms_ 𝒞local)
    (_ : unify (IsGraph.axioms_ 𝒞local) (IsGraph.axioms_ 𝒞) m1 m nomsg)
    (m2 : IsPrecategory.axioms_ 𝒞local m1)
    (_ : unify (IsPrecategory.axioms_ 𝒞local m1) (IsPrecategory.axioms_ 𝒞 m) m2
           m0 nomsg)
    (_ : unify (Precategory.axioms_ 𝒞local) (Precategory.axioms_ 𝒞local)
           (Precategory.Class 𝒞local m1 m2) c nomsg)
    (seqL : has_seqL 𝒞 (@hom (Graph.Pack 𝒞 (Graph.Class 𝒞 m)))
              (@idn (Precategory.Pack 𝒞 (Precategory.Class 𝒞 m m0)))
              (@seq (Precategory.Pack 𝒞 (Precategory.Class 𝒞 m m0))))
    (seqR : has_seqR 𝒞 (@hom (Graph.Pack 𝒞 (Graph.Class 𝒞 m)))
              (@idn (Precategory.Pack 𝒞 (Precategory.Class 𝒞 m m0)))
              (@seq (Precategory.Pack 𝒞 (Precategory.Class 𝒞 m m0))))
    (seqA : has_seqA 𝒞 (@hom (Graph.Pack 𝒞 (Graph.Class 𝒞 m)))
              (@seq (Precategory.Pack 𝒞 (Precategory.Class 𝒞 m m0)))) =>
  Axioms_ 𝒞 m m0 seqL seqR seqA.
Local Arguments phant_Build : clear implicits.
Notation Build X1 := (
  phant_Build X1 _ _ _ (@id_phant _ _) _ (@id_phant _ _) _ (@id_phant _ _) _
    (@id_phant _ _) _ (@id_phant _ _) (@id_phant _ _)).
Definition phant_axioms : forall (𝒞 : Type) (m : IsGraph.axioms_ 𝒞)
                            (m0 : IsPrecategory.axioms_ 𝒞 m) (𝒞local : Type)
                            (_ : unify Type Type 𝒞local 𝒞 nomsg)
                            (s : Precategory.type)
                            (_ : unify Type Type 𝒞local (Precategory.sort s)
                                   (is_not_canonically_a Precategory.type))
                            (c : Precategory.axioms_ 𝒞local)
                            (_ : unify Precategory.type Precategory.type s
                                   (Precategory.Pack 𝒞local c) nomsg)
                            (m1 : IsGraph.axioms_ 𝒞local)
                            (_ : unify (IsGraph.axioms_ 𝒞local)
                                   (IsGraph.axioms_ 𝒞) m1 m nomsg)
                            (m2 : IsPrecategory.axioms_ 𝒞local m1)
                            (_ : unify (IsPrecategory.axioms_ 𝒞local m1)
                                   (IsPrecategory.axioms_ 𝒞 m) m2 m0 nomsg)
                            (_ : unify (Precategory.axioms_ 𝒞local)
                                   (Precategory.axioms_ 𝒞local)
                                   (Precategory.Class 𝒞local m1 m2) c nomsg),
                          Type :=
  fun (𝒞 : Type) (m : IsGraph.axioms_ 𝒞) (m0 : IsPrecategory.axioms_ 𝒞 m)
    (𝒞local : Type) (_ : unify Type Type 𝒞local 𝒞 nomsg) (s : Precategory.type)
    (_ : unify Type Type 𝒞local (Precategory.sort s)
           (is_not_canonically_a Precategory.type))
    (c : Precategory.axioms_ 𝒞local)
    (_ : unify Precategory.type Precategory.type s (Precategory.Pack 𝒞local c)
           nomsg) (m1 : IsGraph.axioms_ 𝒞local)
    (_ : unify (IsGraph.axioms_ 𝒞local) (IsGraph.axioms_ 𝒞) m1 m nomsg)
    (m2 : IsPrecategory.axioms_ 𝒞local m1)
    (_ : unify (IsPrecategory.axioms_ 𝒞local m1) (IsPrecategory.axioms_ 𝒞 m) m2
           m0 nomsg)
    (_ : unify (Precategory.axioms_ 𝒞local) (Precategory.axioms_ 𝒞local)
           (Precategory.Class 𝒞local m1 m2) c nomsg) => axioms_ 𝒞 m m0.
Local Arguments phant_axioms : clear implicits.
Notation axioms X1 := (
  phant_axioms X1 _ _ _ (@id_phant _ _) _ (@id_phant _ _) _ (@id_phant _ _) _
    (@id_phant _ _) _ (@id_phant _ _) (@id_phant _ _)).
Definition identity_builder : forall (𝒞 : Type) (m : IsGraph.axioms_ 𝒞)
                                (m0 : IsPrecategory.axioms_ 𝒞 m)
                                (_ : axioms_ 𝒞 m m0), axioms_ 𝒞 m m0 :=
  fun (𝒞 : Type) (m : IsGraph.axioms_ 𝒞) (m0 : IsPrecategory.axioms_ 𝒞 m)
    (x : axioms_ 𝒞 m m0) => x.
Local Arguments identity_builder : clear implicits.
Module Exports.
Global Arguments Axioms_ {_} {_} {_}.
End Exports.
End IsCategory.
Export IsCategory.Exports.
Notation IsCategory X1 := (
  IsCategory.phant_axioms X1 _ _ _ (@id_phant _ _) _ (@id_phant _ _) _
    (@id_phant _ _) _ (@id_phant _ _) _ (@id_phant _ _) (@id_phant _ _)).
HIERARCHY BUILDER PATCH v1
File "./theories/Category.v", line 41, column 98, characters 1278-1376:
Module Category.
Section axioms_.
Local Unset Implicit Arguments.
Record axioms_ (𝒞 : Type) : Type := Class
  {
    Category_IsGraph_mixin : IsGraph.axioms_ 𝒞;
    Category_IsPrecategory_mixin : IsPrecategory.axioms_ 𝒞
                                     Category_IsGraph_mixin;
    Category_IsCategory_mixin : IsCategory.axioms_ 𝒞 Category_IsGraph_mixin
                                  Category_IsPrecategory_mixin;
    }.
End axioms_.

Global Arguments axioms_ : clear implicits.
Global Arguments Class : clear implicits.
Global Arguments Category_IsGraph_mixin : clear implicits.
Global Arguments Category_IsPrecategory_mixin : clear implicits.
Global Arguments Category_IsCategory_mixin : clear implicits.
Section type.
Local Unset Implicit Arguments.
Record type  : Type := Pack { sort : Type; class : axioms_ sort; }.
End type.

Global Arguments type : clear implicits.
Global Arguments Pack : clear implicits.
Global Arguments sort : clear implicits.
Global Arguments class : clear implicits.
Definition phant_clone : forall (𝒞 : Type) (cT : type) (c : axioms_ 𝒞)
                           (_ : unify Type Type 𝒞 (sort cT) nomsg)
                           (_ : unify type type cT (Pack 𝒞 c) nomsg), type :=
  fun (𝒞 : Type) (cT : type) (c : axioms_ 𝒞)
    (_ : unify Type Type 𝒞 (sort cT) nomsg)
    (_ : unify type type cT (Pack 𝒞 c) nomsg) => Pack 𝒞 c.
Local Arguments phant_clone : clear implicits.
Notation clone X2 X1 := ( phant_clone X2 X1 _ (@id_phant _ _) (@id_phant _ _)).
Definition pack_ :=
  fun (𝒞 : Type) (m : IsGraph.axioms_ 𝒞) (m0 : IsPrecategory.axioms_ 𝒞 m)
    (m1 : IsCategory.axioms_ 𝒞 m m0) => Pack 𝒞 (Class 𝒞 m m0 m1).
Local Arguments pack_ : clear implicits.
Module Exports.
Coercion sort : Category.Category.type >-> Sortclass.
Definition Category_Category_class__to__Category_Graph_class : forall
                                                                 (𝒞 : Type)
                                                                 (_ : 
                                                                  axioms_ 𝒞),
                                                               Graph.axioms_ 𝒞 :=
  fun (𝒞 : Type) (c : axioms_ 𝒞) => Graph.Class 𝒞 (Category_IsGraph_mixin 𝒞 c).
Local Arguments Category_Category_class__to__Category_Graph_class : clear implicits.
Coercion Category_Category_class__to__Category_Graph_class : Category.Category.axioms_ >-> Category.Graph.axioms_.
Definition Category_Category__to__Category_Graph : forall _ : type, Graph.type :=
  fun s : type =>
  Graph.Pack (sort s)
    (Category_Category_class__to__Category_Graph_class (sort s) (class s)).
Local Arguments Category_Category__to__Category_Graph : clear implicits.
Coercion Category_Category__to__Category_Graph : Category.Category.type >-> Category.Graph.type.
Global Canonical Category_Category__to__Category_Graph.
Definition Category_Category_class__to__Category_Precategory_class : 
  forall (𝒞 : Type) (_ : axioms_ 𝒞), Precategory.axioms_ 𝒞 :=
  fun (𝒞 : Type) (c : axioms_ 𝒞) =>
  Precategory.Class 𝒞 (Category_IsGraph_mixin 𝒞 c)
    (Category_IsPrecategory_mixin 𝒞 c).
Local Arguments Category_Category_class__to__Category_Precategory_class : clear implicits.
Coercion Category_Category_class__to__Category_Precategory_class : Category.Category.axioms_ >-> Category.Precategory.axioms_.
Definition Category_Category__to__Category_Precategory : forall _ : type,
                                                         Precategory.type :=
  fun s : type =>
  Precategory.Pack (sort s)
    (Category_Category_class__to__Category_Precategory_class (sort s) (class s)).
Local Arguments Category_Category__to__Category_Precategory : clear implicits.
Coercion Category_Category__to__Category_Precategory : Category.Category.type >-> Category.Precategory.type.
Global Canonical Category_Category__to__Category_Precategory.
Coercion Category_IsGraph_mixin : Category.Category.axioms_ >-> Category.IsGraph.axioms_.
Coercion Category_IsPrecategory_mixin : Category.Category.axioms_ >-> Category.IsPrecategory.axioms_.
Coercion Category_IsCategory_mixin : Category.Category.axioms_ >-> Category.IsCategory.axioms_.
End Exports.
Import Exports.
Definition phant_on_ : forall (𝒞 : type) (_ : phant (sort 𝒞)), axioms_ (sort 𝒞) :=
  fun (𝒞 : type) (_ : phant (sort 𝒞)) => class 𝒞.
Local Arguments phant_on_ : clear implicits.
Notation on_ X1 := ( phant_on_ _ (Phant X1)).
Notation copy X2 X1 := ( phant_on_ _ (Phant X1) : axioms_ X2).
Notation on X1 := ( phant_on_ _ (Phant _) : axioms_ X1).
Module EtaAndMixinExports.
Section hb_instance_12.
Variable 𝒞 : type.
Local Arguments 𝒞 : clear implicits.
Definition HB_unnamed_factory_13 : axioms_ (@eta Type (sort 𝒞)) := class 𝒞.
Local Arguments HB_unnamed_factory_13 : clear implicits.
Definition Category_Category__to__Category_IsGraph : IsGraph.axioms_
                                                       (@eta Type
                                                          (Graph.sort
                                                             (Category_Category__to__Category_Graph
                                                                𝒞))) :=
  HB_unnamed_mixin_4 (Category_Category__to__Category_Graph 𝒞).
Local Arguments Category_Category__to__Category_IsGraph : clear implicits.
Definition Category_Category__to__Category_IsPrecategory : IsPrecategory.axioms_
                                                             (@eta Type
                                                                (Precategory.sort
                                                                   (Category_Category__to__Category_Precategory
                                                                    𝒞)))
                                                             (Precategory.Category_IsGraph_mixin
                                                                (@eta Type
                                                                   (Precategory.sort
                                                                    (Category_Category__to__Category_Precategory
                                                                    𝒞)))
                                                                (HB_unnamed_factory_7
                                                                   (Category_Category__to__Category_Precategory
                                                                    𝒞))) :=
  HB_unnamed_mixin_10 (Category_Category__to__Category_Precategory 𝒞).
Local Arguments Category_Category__to__Category_IsPrecategory : clear implicits.
Definition Category_Category__to__Category_IsCategory : IsCategory.axioms_
                                                          (@eta Type (sort 𝒞))
                                                          (Category_IsGraph_mixin
                                                             (@eta Type
                                                                (sort 𝒞))
                                                             HB_unnamed_factory_13)
                                                          (Category_IsPrecategory_mixin
                                                             (@eta Type
                                                                (sort 𝒞))
                                                             HB_unnamed_factory_13) :=
  Category_IsCategory_mixin (@eta Type (sort 𝒞)) HB_unnamed_factory_13.
Local Arguments Category_Category__to__Category_IsCategory : clear implicits.
Definition HB_unnamed_mixin_17 :=
  Category_IsCategory_mixin (@eta Type (sort 𝒞)) HB_unnamed_factory_13.
Local Arguments HB_unnamed_mixin_17 : clear implicits.
Definition structures_eta__canonical__Category_Category : type :=
  Pack (@eta Type (sort 𝒞))
    (Class (@eta Type (sort 𝒞))
       (HB_unnamed_mixin_4 (Category_Category__to__Category_Graph 𝒞))
       (HB_unnamed_mixin_10 (Category_Category__to__Category_Precategory 𝒞))
       HB_unnamed_mixin_17).
Local Arguments structures_eta__canonical__Category_Category : clear implicits.
Global Canonical structures_eta__canonical__Category_Category.
End hb_instance_12.
End EtaAndMixinExports.
End Category.
Export Category.Exports.
Export Category.EtaAndMixinExports.
Definition seqL : forall s : Category.type,
                  has_seqL (Category.sort s)
                    (@hom
                       (Graph.Pack (Category.sort s)
                          (Graph.Class (Category.sort s)
                             (Category.Category_IsGraph_mixin (Category.sort s)
                                (Category.class s)))))
                    (@idn
                       (Precategory.Pack (Category.sort s)
                          (Precategory.Class (Category.sort s)
                             (Category.Category_IsGraph_mixin (Category.sort s)
                                (Category.class s))
                             (Category.Category_IsPrecategory_mixin
                                (Category.sort s) (Category.class s)))))
                    (@seq
                       (Precategory.Pack (Category.sort s)
                          (Precategory.Class (Category.sort s)
                             (Category.Category_IsGraph_mixin (Category.sort s)
                                (Category.class s))
                             (Category.Category_IsPrecategory_mixin
                                (Category.sort s) (Category.class s))))) :=
  fun s : Category.type =>
  IsCategory.seqL (Category.sort s)
    (Category.Category_IsGraph_mixin (Category.sort s) (Category.class s))
    (Category.Category_IsPrecategory_mixin (Category.sort s) (Category.class s))
    (Category.Category_IsCategory_mixin (Category.sort s) (Category.class s)).
Local Arguments seqL : clear implicits.
Global Arguments seqL {_}.
Definition seqR : forall s : Category.type,
                  has_seqR (Category.sort s)
                    (@hom
                       (Graph.Pack (Category.sort s)
                          (Graph.Class (Category.sort s)
                             (Category.Category_IsGraph_mixin (Category.sort s)
                                (Category.class s)))))
                    (@idn
                       (Precategory.Pack (Category.sort s)
                          (Precategory.Class (Category.sort s)
                             (Category.Category_IsGraph_mixin (Category.sort s)
                                (Category.class s))
                             (Category.Category_IsPrecategory_mixin
                                (Category.sort s) (Category.class s)))))
                    (@seq
                       (Precategory.Pack (Category.sort s)
                          (Precategory.Class (Category.sort s)
                             (Category.Category_IsGraph_mixin (Category.sort s)
                                (Category.class s))
                             (Category.Category_IsPrecategory_mixin
                                (Category.sort s) (Category.class s))))) :=
  fun s : Category.type =>
  IsCategory.seqR (Category.sort s)
    (Category.Category_IsGraph_mixin (Category.sort s) (Category.class s))
    (Category.Category_IsPrecategory_mixin (Category.sort s) (Category.class s))
    (Category.Category_IsCategory_mixin (Category.sort s) (Category.class s)).
Local Arguments seqR : clear implicits.
Global Arguments seqR {_}.
Definition seqA : forall s : Category.type,
                  has_seqA (Category.sort s)
                    (@hom
                       (Graph.Pack (Category.sort s)
                          (Graph.Class (Category.sort s)
                             (Category.Category_IsGraph_mixin (Category.sort s)
                                (Category.class s)))))
                    (@seq
                       (Precategory.Pack (Category.sort s)
                          (Precategory.Class (Category.sort s)
                             (Category.Category_IsGraph_mixin (Category.sort s)
                                (Category.class s))
                             (Category.Category_IsPrecategory_mixin
                                (Category.sort s) (Category.class s))))) :=
  fun s : Category.type =>
  IsCategory.seqA (Category.sort s)
    (Category.Category_IsGraph_mixin (Category.sort s) (Category.class s))
    (Category.Category_IsPrecategory_mixin (Category.sort s) (Category.class s))
    (Category.Category_IsCategory_mixin (Category.sort s) (Category.class s)).
Local Arguments seqA : clear implicits.
Global Arguments seqA {_}.
Module ElpiOperations18.
End ElpiOperations18.
Export ElpiOperations18.
Notation Category X1 := ( Category.axioms_ X1).
HIERARCHY BUILDER PATCH v1
File "./theories/Category.v", line 5, column 71, characters 74-145:
Module IsGraph.
Section IsGraph.
Variable obj : Type.
Local Arguments obj : clear implicits.
Section axioms_.
Local Unset Implicit Arguments.
Record axioms_ (obj : Type) : Type := Axioms_
  { hom : forall (_ : obj) (_ : obj), Type; }.
End axioms_.

Global Arguments axioms_ : clear implicits.
Global Arguments Axioms_ : clear implicits.
Global Arguments hom : clear implicits.
End IsGraph.
Global Arguments axioms_ : clear implicits.
Global Arguments Axioms_ : clear implicits.
Definition phant_Build : forall (obj : Type)
                           (_ : forall (_ : obj) (_ : obj), Type), axioms_ obj :=
  fun (obj : Type) (hom : forall (_ : obj) (_ : obj), Type) => Axioms_ obj hom.
Local Arguments phant_Build : clear implicits.
Notation Build X1 := ( phant_Build X1).
Definition phant_axioms : forall _ : Type, Type :=
  fun obj : Type => axioms_ obj.
Local Arguments phant_axioms : clear implicits.
Notation axioms X1 := ( phant_axioms X1).
Definition identity_builder : forall (obj : Type) (_ : axioms_ obj),
                              axioms_ obj :=
  fun (obj : Type) (x : axioms_ obj) => x.
Local Arguments identity_builder : clear implicits.
Module Exports.
Global Arguments Axioms_ {_}.
End Exports.
End IsGraph.
Export IsGraph.Exports.
Notation IsGraph X1 := ( IsGraph.phant_axioms X1).
HIERARCHY BUILDER PATCH v1
File "./theories/Category.v", line 10, column 56, characters 149-205:
Module Graph.
Section axioms_.
Local Unset Implicit Arguments.
Record axioms_ (𝒞 : Type) : Type := Class
  { Category_IsGraph_mixin : IsGraph.axioms_ 𝒞; }.
End axioms_.

Global Arguments axioms_ : clear implicits.
Global Arguments Class : clear implicits.
Global Arguments Category_IsGraph_mixin : clear implicits.
Section type.
Local Unset Implicit Arguments.
Record type  : Type := Pack { sort : Type; class : axioms_ sort; }.
End type.

Global Arguments type : clear implicits.
Global Arguments Pack : clear implicits.
Global Arguments sort : clear implicits.
Global Arguments class : clear implicits.
Definition phant_clone : forall (𝒞 : Type) (cT : type) (c : axioms_ 𝒞)
                           (_ : unify Type Type 𝒞 (sort cT) nomsg)
                           (_ : unify type type cT (Pack 𝒞 c) nomsg), type :=
  fun (𝒞 : Type) (cT : type) (c : axioms_ 𝒞)
    (_ : unify Type Type 𝒞 (sort cT) nomsg)
    (_ : unify type type cT (Pack 𝒞 c) nomsg) => Pack 𝒞 c.
Local Arguments phant_clone : clear implicits.
Notation clone X2 X1 := ( phant_clone X2 X1 _ (@id_phant _ _) (@id_phant _ _)).
Definition pack_ :=
  fun (𝒞 : Type) (m : IsGraph.axioms_ 𝒞) => Pack 𝒞 (Class 𝒞 m).
Local Arguments pack_ : clear implicits.
Module Exports.
Coercion sort : Category.Graph.type >-> Sortclass.
Coercion Category_IsGraph_mixin : Category.Graph.axioms_ >-> Category.IsGraph.axioms_.
End Exports.
Import Exports.
Definition phant_on_ : forall (𝒞 : type) (_ : phant (sort 𝒞)), axioms_ (sort 𝒞) :=
  fun (𝒞 : type) (_ : phant (sort 𝒞)) => class 𝒞.
Local Arguments phant_on_ : clear implicits.
Notation on_ X1 := ( phant_on_ _ (Phant X1)).
Notation copy X2 X1 := ( phant_on_ _ (Phant X1) : axioms_ X2).
Notation on X1 := ( phant_on_ _ (Phant _) : axioms_ X1).
Module EtaAndMixinExports.
Section hb_instance_1.
Variable 𝒞 : type.
Local Arguments 𝒞 : clear implicits.
Definition HB_unnamed_factory_2 : axioms_ (@eta Type (sort 𝒞)) := class 𝒞.
Local Arguments HB_unnamed_factory_2 : clear implicits.
Definition Category_Graph__to__Category_IsGraph : IsGraph.axioms_
                                                    (@eta Type (sort 𝒞)) :=
  Category_IsGraph_mixin (@eta Type (sort 𝒞)) HB_unnamed_factory_2.
Local Arguments Category_Graph__to__Category_IsGraph : clear implicits.
Definition HB_unnamed_mixin_4 :=
  Category_IsGraph_mixin (@eta Type (sort 𝒞)) HB_unnamed_factory_2.
Local Arguments HB_unnamed_mixin_4 : clear implicits.
Definition structures_eta__canonical__Category_Graph : type :=
  Pack (@eta Type (sort 𝒞)) (Class (@eta Type (sort 𝒞)) HB_unnamed_mixin_4).
Local Arguments structures_eta__canonical__Category_Graph : clear implicits.
Global Canonical structures_eta__canonical__Category_Graph.
End hb_instance_1.
End EtaAndMixinExports.
End Graph.
Export Graph.Exports.
Export Graph.EtaAndMixinExports.
Definition hom : forall (s : Graph.type) (_ : Graph.sort s) (_ : Graph.sort s),
                 Type :=
  fun (s : Graph.type) (H H0 : Graph.sort s) =>
  IsGraph.hom (Graph.sort s)
    (Graph.Category_IsGraph_mixin (Graph.sort s) (Graph.class s)) H H0.
Local Arguments hom : clear implicits.
Global Arguments hom {_}.
Module ElpiOperations5.
End ElpiOperations5.
Export ElpiOperations5.
Notation Graph X1 := ( Graph.axioms_ X1).
HIERARCHY BUILDER PATCH v1
File "./theories/Category.v", line 14, column 142, characters 241-383:
Module IsPrecategory.
Section IsPrecategory.
Variable 𝒞 : Type.
Local Arguments 𝒞 : clear implicits.
Variable local_mixin_Category_IsGraph : IsGraph.axioms_ 𝒞.
Local Arguments local_mixin_Category_IsGraph : clear implicits.
Definition IsPrecategory_𝒞__canonical__Category_Graph : Graph.type :=
  Graph.Pack 𝒞 (Graph.Class 𝒞 local_mixin_Category_IsGraph).
Local Arguments IsPrecategory_𝒞__canonical__Category_Graph : clear implicits.
Local Canonical IsPrecategory_𝒞__canonical__Category_Graph.
Section axioms_.
Local Unset Implicit Arguments.
Record axioms_
    (𝒞 : Type)(local_mixin_Category_IsGraph : IsGraph.axioms_ 𝒞) : Type
  := Axioms_
  {
    idn : forall x : 𝒞,
          @hom (Graph.Pack 𝒞 (Graph.Class 𝒞 local_mixin_Category_IsGraph)) x x;
    seq : forall (x y z : 𝒞)
            (_ : @hom
                   (Graph.Pack 𝒞 (Graph.Class 𝒞 local_mixin_Category_IsGraph))
                   x y)
            (_ : @hom
                   (Graph.Pack 𝒞 (Graph.Class 𝒞 local_mixin_Category_IsGraph))
                   y z),
          @hom (Graph.Pack 𝒞 (Graph.Class 𝒞 local_mixin_Category_IsGraph)) x z;
    }.
End axioms_.

Global Arguments axioms_ : clear implicits.
Global Arguments Axioms_ : clear implicits.
Global Arguments idn : clear implicits.
Global Arguments seq : clear implicits.
End IsPrecategory.
Global Arguments axioms_ : clear implicits.
Global Arguments Axioms_ : clear implicits.
Definition phant_Build : forall (𝒞 : Type) (m : IsGraph.axioms_ 𝒞)
                           (𝒞local : Type) (_ : unify Type Type 𝒞local 𝒞 nomsg)
                           (s : Graph.type)
                           (_ : unify Type Type 𝒞local (Graph.sort s)
                                  (is_not_canonically_a Graph.type))
                           (c : Graph.axioms_ 𝒞local)
                           (_ : unify Graph.type Graph.type s
                                  (Graph.Pack 𝒞local c) nomsg)
                           (m0 : IsGraph.axioms_ 𝒞local)
                           (_ : unify (IsGraph.axioms_ 𝒞local)
                                  (IsGraph.axioms_ 𝒞) m0 m nomsg)
                           (_ : unify (Graph.axioms_ 𝒞local)
                                  (Graph.axioms_ 𝒞local)
                                  (Graph.Class 𝒞local m0) c nomsg)
                           (_ : forall x : 𝒞,
                                @hom (Graph.Pack 𝒞 (Graph.Class 𝒞 m)) x x)
                           (_ : forall (x y z : 𝒞)
                                  (_ : @hom (Graph.Pack 𝒞 (Graph.Class 𝒞 m)) x
                                         y)
                                  (_ : @hom (Graph.Pack 𝒞 (Graph.Class 𝒞 m)) y
                                         z),
                                @hom (Graph.Pack 𝒞 (Graph.Class 𝒞 m)) x z),
                         axioms_ 𝒞 m :=
  fun (𝒞 : Type) (m : IsGraph.axioms_ 𝒞) (𝒞local : Type)
    (_ : unify Type Type 𝒞local 𝒞 nomsg) (s : Graph.type)
    (_ : unify Type Type 𝒞local (Graph.sort s)
           (is_not_canonically_a Graph.type)) (c : Graph.axioms_ 𝒞local)
    (_ : unify Graph.type Graph.type s (Graph.Pack 𝒞local c) nomsg)
    (m0 : IsGraph.axioms_ 𝒞local)
    (_ : unify (IsGraph.axioms_ 𝒞local) (IsGraph.axioms_ 𝒞) m0 m nomsg)
    (_ : unify (Graph.axioms_ 𝒞local) (Graph.axioms_ 𝒞local)
           (Graph.Class 𝒞local m0) c nomsg)
    (idn : forall x : 𝒞, @hom (Graph.Pack 𝒞 (Graph.Class 𝒞 m)) x x)
    (seq : forall (x y z : 𝒞) (_ : @hom (Graph.Pack 𝒞 (Graph.Class 𝒞 m)) x y)
             (_ : @hom (Graph.Pack 𝒞 (Graph.Class 𝒞 m)) y z),
           @hom (Graph.Pack 𝒞 (Graph.Class 𝒞 m)) x z) => Axioms_ 𝒞 m idn seq.
Local Arguments phant_Build : clear implicits.
Notation Build X1 := (
  phant_Build X1 _ _ (@id_phant _ _) _ (@id_phant _ _) _ (@id_phant _ _) _
    (@id_phant _ _) (@id_phant _ _)).
Definition phant_axioms : forall (𝒞 : Type) (m : IsGraph.axioms_ 𝒞)
                            (𝒞local : Type)
                            (_ : unify Type Type 𝒞local 𝒞 nomsg)
                            (s : Graph.type)
                            (_ : unify Type Type 𝒞local (Graph.sort s)
                                   (is_not_canonically_a Graph.type))
                            (c : Graph.axioms_ 𝒞local)
                            (_ : unify Graph.type Graph.type s
                                   (Graph.Pack 𝒞local c) nomsg)
                            (m0 : IsGraph.axioms_ 𝒞local)
                            (_ : unify (IsGraph.axioms_ 𝒞local)
                                   (IsGraph.axioms_ 𝒞) m0 m nomsg)
                            (_ : unify (Graph.axioms_ 𝒞local)
                                   (Graph.axioms_ 𝒞local)
                                   (Graph.Class 𝒞local m0) c nomsg), Type :=
  fun (𝒞 : Type) (m : IsGraph.axioms_ 𝒞) (𝒞local : Type)
    (_ : unify Type Type 𝒞local 𝒞 nomsg) (s : Graph.type)
    (_ : unify Type Type 𝒞local (Graph.sort s)
           (is_not_canonically_a Graph.type)) (c : Graph.axioms_ 𝒞local)
    (_ : unify Graph.type Graph.type s (Graph.Pack 𝒞local c) nomsg)
    (m0 : IsGraph.axioms_ 𝒞local)
    (_ : unify (IsGraph.axioms_ 𝒞local) (IsGraph.axioms_ 𝒞) m0 m nomsg)
    (_ : unify (Graph.axioms_ 𝒞local) (Graph.axioms_ 𝒞local)
           (Graph.Class 𝒞local m0) c nomsg) => axioms_ 𝒞 m.
Local Arguments phant_axioms : clear implicits.
Notation axioms X1 := (
  phant_axioms X1 _ _ (@id_phant _ _) _ (@id_phant _ _) _ (@id_phant _ _) _
    (@id_phant _ _) (@id_phant _ _)).
Definition identity_builder : forall (𝒞 : Type) (m : IsGraph.axioms_ 𝒞)
                                (_ : axioms_ 𝒞 m), axioms_ 𝒞 m :=
  fun (𝒞 : Type) (m : IsGraph.axioms_ 𝒞) (x : axioms_ 𝒞 m) => x.
Local Arguments identity_builder : clear implicits.
Module Exports.
Global Arguments Axioms_ {_} {_}.
End Exports.
End IsPrecategory.
Export IsPrecategory.Exports.
Notation IsPrecategory X1 := (
  IsPrecategory.phant_axioms X1 _ _ (@id_phant _ _) _ (@id_phant _ _) _
    (@id_phant _ _) _ (@id_phant _ _) (@id_phant _ _)).
HIERARCHY BUILDER PATCH v1
File "./theories/Category.v", line 18, column 83, characters 385-468:
Module Precategory.
Section axioms_.
Local Unset Implicit Arguments.
Record axioms_ (𝒞 : Type) : Type := Class
  {
    Category_IsGraph_mixin : IsGraph.axioms_ 𝒞;
    Category_IsPrecategory_mixin : IsPrecategory.axioms_ 𝒞
                                     Category_IsGraph_mixin;
    }.
End axioms_.

Global Arguments axioms_ : clear implicits.
Global Arguments Class : clear implicits.
Global Arguments Category_IsGraph_mixin : clear implicits.
Global Arguments Category_IsPrecategory_mixin : clear implicits.
Section type.
Local Unset Implicit Arguments.
Record type  : Type := Pack { sort : Type; class : axioms_ sort; }.
End type.

Global Arguments type : clear implicits.
Global Arguments Pack : clear implicits.
Global Arguments sort : clear implicits.
Global Arguments class : clear implicits.
Definition phant_clone : forall (𝒞 : Type) (cT : type) (c : axioms_ 𝒞)
                           (_ : unify Type Type 𝒞 (sort cT) nomsg)
                           (_ : unify type type cT (Pack 𝒞 c) nomsg), type :=
  fun (𝒞 : Type) (cT : type) (c : axioms_ 𝒞)
    (_ : unify Type Type 𝒞 (sort cT) nomsg)
    (_ : unify type type cT (Pack 𝒞 c) nomsg) => Pack 𝒞 c.
Local Arguments phant_clone : clear implicits.
Notation clone X2 X1 := ( phant_clone X2 X1 _ (@id_phant _ _) (@id_phant _ _)).
Definition pack_ :=
  fun (𝒞 : Type) (m : IsGraph.axioms_ 𝒞) (m0 : IsPrecategory.axioms_ 𝒞 m) =>
  Pack 𝒞 (Class 𝒞 m m0).
Local Arguments pack_ : clear implicits.
Module Exports.
Coercion sort : Category.Precategory.type >-> Sortclass.
Definition Category_Precategory_class__to__Category_Graph_class : forall
                                                                    (𝒞 : Type)
                                                                    (_ : 
                                                                    axioms_ 𝒞),
                                                                  Graph.axioms_
                                                                    𝒞 :=
  fun (𝒞 : Type) (c : axioms_ 𝒞) => Graph.Class 𝒞 (Category_IsGraph_mixin 𝒞 c).
Local Arguments Category_Precategory_class__to__Category_Graph_class : clear implicits.
Coercion Category_Precategory_class__to__Category_Graph_class : Category.Precategory.axioms_ >-> Category.Graph.axioms_.
Definition Category_Precategory__to__Category_Graph : forall _ : type,
                                                      Graph.type :=
  fun s : type =>
  Graph.Pack (sort s)
    (Category_Precategory_class__to__Category_Graph_class (sort s) (class s)).
Local Arguments Category_Precategory__to__Category_Graph : clear implicits.
Coercion Category_Precategory__to__Category_Graph : Category.Precategory.type >-> Category.Graph.type.
Global Canonical Category_Precategory__to__Category_Graph.
Coercion Category_IsGraph_mixin : Category.Precategory.axioms_ >-> Category.IsGraph.axioms_.
Coercion Category_IsPrecategory_mixin : Category.Precategory.axioms_ >-> Category.IsPrecategory.axioms_.
End Exports.
Import Exports.
Definition phant_on_ : forall (𝒞 : type) (_ : phant (sort 𝒞)), axioms_ (sort 𝒞) :=
  fun (𝒞 : type) (_ : phant (sort 𝒞)) => class 𝒞.
Local Arguments phant_on_ : clear implicits.
Notation on_ X1 := ( phant_on_ _ (Phant X1)).
Notation copy X2 X1 := ( phant_on_ _ (Phant X1) : axioms_ X2).
Notation on X1 := ( phant_on_ _ (Phant _) : axioms_ X1).
Module EtaAndMixinExports.
Section hb_instance_6.
Variable 𝒞 : type.
Local Arguments 𝒞 : clear implicits.
Definition HB_unnamed_factory_7 : axioms_ (@eta Type (sort 𝒞)) := class 𝒞.
Local Arguments HB_unnamed_factory_7 : clear implicits.
Definition Category_Precategory__to__Category_IsGraph : IsGraph.axioms_
                                                          (@eta Type
                                                             (Graph.sort
                                                                (Category_Precategory__to__Category_Graph
                                                                   𝒞))) :=
  HB_unnamed_mixin_4 (Category_Precategory__to__Category_Graph 𝒞).
Local Arguments Category_Precategory__to__Category_IsGraph : clear implicits.
Definition Category_Precategory__to__Category_IsPrecategory : IsPrecategory.axioms_
                                                                (@eta Type
                                                                   (sort 𝒞))
                                                                (Category_IsGraph_mixin
                                                                   (@eta Type
                                                                    (sort 𝒞))
                                                                   HB_unnamed_factory_7) :=
  Category_IsPrecategory_mixin (@eta Type (sort 𝒞)) HB_unnamed_factory_7.
Local Arguments Category_Precategory__to__Category_IsPrecategory : clear implicits.
Definition HB_unnamed_mixin_10 :=
  Category_IsPrecategory_mixin (@eta Type (sort 𝒞)) HB_unnamed_factory_7.
Local Arguments HB_unnamed_mixin_10 : clear implicits.
Definition structures_eta__canonical__Category_Precategory : type :=
  Pack (@eta Type (sort 𝒞))
    (Class (@eta Type (sort 𝒞))
       (HB_unnamed_mixin_4 (Category_Precategory__to__Category_Graph 𝒞))
       HB_unnamed_mixin_10).
Local Arguments structures_eta__canonical__Category_Precategory : clear implicits.
Global Canonical structures_eta__canonical__Category_Precategory.
End hb_instance_6.
End EtaAndMixinExports.
End Precategory.
Export Precategory.Exports.
Export Precategory.EtaAndMixinExports.
Definition idn : forall (s : Precategory.type) (x : Precategory.sort s),
                 @hom
                   (Graph.Pack (Precategory.sort s)
                      (Graph.Class (Precategory.sort s)
                         (Precategory.Category_IsGraph_mixin
                            (Precategory.sort s) (Precategory.class s)))) x x :=
  fun (s : Precategory.type) (x : Precategory.sort s) =>
  IsPrecategory.idn (Precategory.sort s)
    (Precategory.Category_IsGraph_mixin (Precategory.sort s)
       (Precategory.class s))
    (Precategory.Category_IsPrecategory_mixin (Precategory.sort s)
       (Precategory.class s)) x.
Local Arguments idn : clear implicits.
Global Arguments idn {_}.
Definition seq : forall (s : Precategory.type) (x y z : Precategory.sort s)
                   (_ : @hom
                          (Graph.Pack (Precategory.sort s)
                             (Graph.Class (Precategory.sort s)
                                (Precategory.Category_IsGraph_mixin
                                   (Precategory.sort s) (Precategory.class s))))
                          x y)
                   (_ : @hom
                          (Graph.Pack (Precategory.sort s)
                             (Graph.Class (Precategory.sort s)
                                (Precategory.Category_IsGraph_mixin
                                   (Precategory.sort s) (Precategory.class s))))
                          y z),
                 @hom
                   (Graph.Pack (Precategory.sort s)
                      (Graph.Class (Precategory.sort s)
                         (Precategory.Category_IsGraph_mixin
                            (Precategory.sort s) (Precategory.class s)))) x z :=
  fun (s : Precategory.type) (x y z : Precategory.sort s)
    (H : @hom
           (Graph.Pack (Precategory.sort s)
              (Graph.Class (Precategory.sort s)
                 (Precategory.Category_IsGraph_mixin (Precategory.sort s)
                    (Precategory.class s)))) x y)
    (H0 : @hom
            (Graph.Pack (Precategory.sort s)
               (Graph.Class (Precategory.sort s)
                  (Precategory.Category_IsGraph_mixin (Precategory.sort s)
                     (Precategory.class s)))) y z) =>
  IsPrecategory.seq (Precategory.sort s)
    (Precategory.Category_IsGraph_mixin (Precategory.sort s)
       (Precategory.class s))
    (Precategory.Category_IsPrecategory_mixin (Precategory.sort s)
       (Precategory.class s)) x y z H H0.
Local Arguments seq : clear implicits.
Global Arguments seq {_}.
Module ElpiOperations11.
End ElpiOperations11.
Export ElpiOperations11.
Notation Precategory X1 := ( Precategory.axioms_ X1).
HIERARCHY BUILDER PATCH v1
File "./theories/Category.v", line 31, column 162, characters 1013-1175:
Module IsCategory.
Section IsCategory.
Variable 𝒞 : Type.
Local Arguments 𝒞 : clear implicits.
Variable local_mixin_Category_IsGraph : IsGraph.axioms_ 𝒞.
Local Arguments local_mixin_Category_IsGraph : clear implicits.
Variable local_mixin_Category_IsPrecategory :
  IsPrecategory.axioms_ 𝒞 local_mixin_Category_IsGraph.
Local Arguments local_mixin_Category_IsPrecategory : clear implicits.
Definition IsCategory_𝒞__canonical__Category_Graph : Graph.type :=
  Graph.Pack 𝒞 (Graph.Class 𝒞 local_mixin_Category_IsGraph).
Local Arguments IsCategory_𝒞__canonical__Category_Graph : clear implicits.
Local Canonical IsCategory_𝒞__canonical__Category_Graph.
Definition IsCategory_𝒞__canonical__Category_Precategory : Precategory.type :=
  Precategory.Pack 𝒞
    (Precategory.Class 𝒞 local_mixin_Category_IsGraph
       local_mixin_Category_IsPrecategory).
Local Arguments IsCategory_𝒞__canonical__Category_Precategory : clear implicits.
Local Canonical IsCategory_𝒞__canonical__Category_Precategory.
Section axioms_.
Local Unset Implicit Arguments.
Record axioms_
    (𝒞 : Type)(local_mixin_Category_IsGraph : IsGraph.axioms_ 𝒞)(local_mixin_Category_IsPrecategory : 
                                                                  IsPrecategory.axioms_
                                                                    𝒞
                                                                    local_mixin_Category_IsGraph) : Type
  := Axioms_
  {
    seqL : has_seqL 𝒞
             (@hom (Graph.Pack 𝒞 (Graph.Class 𝒞 local_mixin_Category_IsGraph)))
             (@idn
                (Precategory.Pack 𝒞
                   (Precategory.Class 𝒞 local_mixin_Category_IsGraph
                      local_mixin_Category_IsPrecategory)))
             (@seq
                (Precategory.Pack 𝒞
                   (Precategory.Class 𝒞 local_mixin_Category_IsGraph
                      local_mixin_Category_IsPrecategory)));
    seqR : has_seqR 𝒞
             (@hom (Graph.Pack 𝒞 (Graph.Class 𝒞 local_mixin_Category_IsGraph)))
             (@idn
                (Precategory.Pack 𝒞
                   (Precategory.Class 𝒞 local_mixin_Category_IsGraph
                      local_mixin_Category_IsPrecategory)))
             (@seq
                (Precategory.Pack 𝒞
                   (Precategory.Class 𝒞 local_mixin_Category_IsGraph
                      local_mixin_Category_IsPrecategory)));
    seqA : has_seqA 𝒞
             (@hom (Graph.Pack 𝒞 (Graph.Class 𝒞 local_mixin_Category_IsGraph)))
             (@seq
                (Precategory.Pack 𝒞
                   (Precategory.Class 𝒞 local_mixin_Category_IsGraph
                      local_mixin_Category_IsPrecategory)));
    }.
End axioms_.

Global Arguments axioms_ : clear implicits.
Global Arguments Axioms_ : clear implicits.
Global Arguments seqL : clear implicits.
Global Arguments seqR : clear implicits.
Global Arguments seqA : clear implicits.
End IsCategory.
Global Arguments axioms_ : clear implicits.
Global Arguments Axioms_ : clear implicits.
Definition phant_Build : forall (𝒞 : Type) (m : IsGraph.axioms_ 𝒞)
                           (m0 : IsPrecategory.axioms_ 𝒞 m) (𝒞local : Type)
                           (_ : unify Type Type 𝒞local 𝒞 nomsg)
                           (s : Precategory.type)
                           (_ : unify Type Type 𝒞local (Precategory.sort s)
                                  (is_not_canonically_a Precategory.type))
                           (c : Precategory.axioms_ 𝒞local)
                           (_ : unify Precategory.type Precategory.type s
                                  (Precategory.Pack 𝒞local c) nomsg)
                           (m1 : IsGraph.axioms_ 𝒞local)
                           (_ : unify (IsGraph.axioms_ 𝒞local)
                                  (IsGraph.axioms_ 𝒞) m1 m nomsg)
                           (m2 : IsPrecategory.axioms_ 𝒞local m1)
                           (_ : unify (IsPrecategory.axioms_ 𝒞local m1)
                                  (IsPrecategory.axioms_ 𝒞 m) m2 m0 nomsg)
                           (_ : unify (Precategory.axioms_ 𝒞local)
                                  (Precategory.axioms_ 𝒞local)
                                  (Precategory.Class 𝒞local m1 m2) c nomsg)
                           (_ : has_seqL 𝒞
                                  (@hom (Graph.Pack 𝒞 (Graph.Class 𝒞 m)))
                                  (@idn
                                     (Precategory.Pack 𝒞
                                        (Precategory.Class 𝒞 m m0)))
                                  (@seq
                                     (Precategory.Pack 𝒞
                                        (Precategory.Class 𝒞 m m0))))
                           (_ : has_seqR 𝒞
                                  (@hom (Graph.Pack 𝒞 (Graph.Class 𝒞 m)))
                                  (@idn
                                     (Precategory.Pack 𝒞
                                        (Precategory.Class 𝒞 m m0)))
                                  (@seq
                                     (Precategory.Pack 𝒞
                                        (Precategory.Class 𝒞 m m0))))
                           (_ : has_seqA 𝒞
                                  (@hom (Graph.Pack 𝒞 (Graph.Class 𝒞 m)))
                                  (@seq
                                     (Precategory.Pack 𝒞
                                        (Precategory.Class 𝒞 m m0)))),
                         axioms_ 𝒞 m m0 :=
  fun (𝒞 : Type) (m : IsGraph.axioms_ 𝒞) (m0 : IsPrecategory.axioms_ 𝒞 m)
    (𝒞local : Type) (_ : unify Type Type 𝒞local 𝒞 nomsg) (s : Precategory.type)
    (_ : unify Type Type 𝒞local (Precategory.sort s)
           (is_not_canonically_a Precategory.type))
    (c : Precategory.axioms_ 𝒞local)
    (_ : unify Precategory.type Precategory.type s (Precategory.Pack 𝒞local c)
           nomsg) (m1 : IsGraph.axioms_ 𝒞local)
    (_ : unify (IsGraph.axioms_ 𝒞local) (IsGraph.axioms_ 𝒞) m1 m nomsg)
    (m2 : IsPrecategory.axioms_ 𝒞local m1)
    (_ : unify (IsPrecategory.axioms_ 𝒞local m1) (IsPrecategory.axioms_ 𝒞 m) m2
           m0 nomsg)
    (_ : unify (Precategory.axioms_ 𝒞local) (Precategory.axioms_ 𝒞local)
           (Precategory.Class 𝒞local m1 m2) c nomsg)
    (seqL : has_seqL 𝒞 (@hom (Graph.Pack 𝒞 (Graph.Class 𝒞 m)))
              (@idn (Precategory.Pack 𝒞 (Precategory.Class 𝒞 m m0)))
              (@seq (Precategory.Pack 𝒞 (Precategory.Class 𝒞 m m0))))
    (seqR : has_seqR 𝒞 (@hom (Graph.Pack 𝒞 (Graph.Class 𝒞 m)))
              (@idn (Precategory.Pack 𝒞 (Precategory.Class 𝒞 m m0)))
              (@seq (Precategory.Pack 𝒞 (Precategory.Class 𝒞 m m0))))
    (seqA : has_seqA 𝒞 (@hom (Graph.Pack 𝒞 (Graph.Class 𝒞 m)))
              (@seq (Precategory.Pack 𝒞 (Precategory.Class 𝒞 m m0)))) =>
  Axioms_ 𝒞 m m0 seqL seqR seqA.
Local Arguments phant_Build : clear implicits.
Notation Build X1 := (
  phant_Build X1 _ _ _ (@id_phant _ _) _ (@id_phant _ _) _ (@id_phant _ _) _
    (@id_phant _ _) _ (@id_phant _ _) (@id_phant _ _)).
Definition phant_axioms : forall (𝒞 : Type) (m : IsGraph.axioms_ 𝒞)
                            (m0 : IsPrecategory.axioms_ 𝒞 m) (𝒞local : Type)
                            (_ : unify Type Type 𝒞local 𝒞 nomsg)
                            (s : Precategory.type)
                            (_ : unify Type Type 𝒞local (Precategory.sort s)
                                   (is_not_canonically_a Precategory.type))
                            (c : Precategory.axioms_ 𝒞local)
                            (_ : unify Precategory.type Precategory.type s
                                   (Precategory.Pack 𝒞local c) nomsg)
                            (m1 : IsGraph.axioms_ 𝒞local)
                            (_ : unify (IsGraph.axioms_ 𝒞local)
                                   (IsGraph.axioms_ 𝒞) m1 m nomsg)
                            (m2 : IsPrecategory.axioms_ 𝒞local m1)
                            (_ : unify (IsPrecategory.axioms_ 𝒞local m1)
                                   (IsPrecategory.axioms_ 𝒞 m) m2 m0 nomsg)
                            (_ : unify (Precategory.axioms_ 𝒞local)
                                   (Precategory.axioms_ 𝒞local)
                                   (Precategory.Class 𝒞local m1 m2) c nomsg),
                          Type :=
  fun (𝒞 : Type) (m : IsGraph.axioms_ 𝒞) (m0 : IsPrecategory.axioms_ 𝒞 m)
    (𝒞local : Type) (_ : unify Type Type 𝒞local 𝒞 nomsg) (s : Precategory.type)
    (_ : unify Type Type 𝒞local (Precategory.sort s)
           (is_not_canonically_a Precategory.type))
    (c : Precategory.axioms_ 𝒞local)
    (_ : unify Precategory.type Precategory.type s (Precategory.Pack 𝒞local c)
           nomsg) (m1 : IsGraph.axioms_ 𝒞local)
    (_ : unify (IsGraph.axioms_ 𝒞local) (IsGraph.axioms_ 𝒞) m1 m nomsg)
    (m2 : IsPrecategory.axioms_ 𝒞local m1)
    (_ : unify (IsPrecategory.axioms_ 𝒞local m1) (IsPrecategory.axioms_ 𝒞 m) m2
           m0 nomsg)
    (_ : unify (Precategory.axioms_ 𝒞local) (Precategory.axioms_ 𝒞local)
           (Precategory.Class 𝒞local m1 m2) c nomsg) => axioms_ 𝒞 m m0.
Local Arguments phant_axioms : clear implicits.
Notation axioms X1 := (
  phant_axioms X1 _ _ _ (@id_phant _ _) _ (@id_phant _ _) _ (@id_phant _ _) _
    (@id_phant _ _) _ (@id_phant _ _) (@id_phant _ _)).
Definition identity_builder : forall (𝒞 : Type) (m : IsGraph.axioms_ 𝒞)
                                (m0 : IsPrecategory.axioms_ 𝒞 m)
                                (_ : axioms_ 𝒞 m m0), axioms_ 𝒞 m m0 :=
  fun (𝒞 : Type) (m : IsGraph.axioms_ 𝒞) (m0 : IsPrecategory.axioms_ 𝒞 m)
    (x : axioms_ 𝒞 m m0) => x.
Local Arguments identity_builder : clear implicits.
Module Exports.
Global Arguments Axioms_ {_} {_} {_}.
End Exports.
End IsCategory.
Export IsCategory.Exports.
Notation IsCategory X1 := (
  IsCategory.phant_axioms X1 _ _ _ (@id_phant _ _) _ (@id_phant _ _) _
    (@id_phant _ _) _ (@id_phant _ _) _ (@id_phant _ _) (@id_phant _ _)).
HIERARCHY BUILDER PATCH v1
File "./theories/Category.v", line 36, column 98, characters 1177-1275:
Module Category.
Section axioms_.
Local Unset Implicit Arguments.
Record axioms_ (𝒞 : Type) : Type := Class
  {
    Category_IsGraph_mixin : IsGraph.axioms_ 𝒞;
    Category_IsPrecategory_mixin : IsPrecategory.axioms_ 𝒞
                                     Category_IsGraph_mixin;
    Category_IsCategory_mixin : IsCategory.axioms_ 𝒞 Category_IsGraph_mixin
                                  Category_IsPrecategory_mixin;
    }.
End axioms_.

Global Arguments axioms_ : clear implicits.
Global Arguments Class : clear implicits.
Global Arguments Category_IsGraph_mixin : clear implicits.
Global Arguments Category_IsPrecategory_mixin : clear implicits.
Global Arguments Category_IsCategory_mixin : clear implicits.
Section type.
Local Unset Implicit Arguments.
Record type  : Type := Pack { sort : Type; class : axioms_ sort; }.
End type.

Global Arguments type : clear implicits.
Global Arguments Pack : clear implicits.
Global Arguments sort : clear implicits.
Global Arguments class : clear implicits.
Definition phant_clone : forall (𝒞 : Type) (cT : type) (c : axioms_ 𝒞)
                           (_ : unify Type Type 𝒞 (sort cT) nomsg)
                           (_ : unify type type cT (Pack 𝒞 c) nomsg), type :=
  fun (𝒞 : Type) (cT : type) (c : axioms_ 𝒞)
    (_ : unify Type Type 𝒞 (sort cT) nomsg)
    (_ : unify type type cT (Pack 𝒞 c) nomsg) => Pack 𝒞 c.
Local Arguments phant_clone : clear implicits.
Notation clone X2 X1 := ( phant_clone X2 X1 _ (@id_phant _ _) (@id_phant _ _)).
Definition pack_ :=
  fun (𝒞 : Type) (m : IsGraph.axioms_ 𝒞) (m0 : IsPrecategory.axioms_ 𝒞 m)
    (m1 : IsCategory.axioms_ 𝒞 m m0) => Pack 𝒞 (Class 𝒞 m m0 m1).
Local Arguments pack_ : clear implicits.
Module Exports.
Coercion sort : Category.Category.type >-> Sortclass.
Definition Category_Category_class__to__Category_Graph_class : forall
                                                                 (𝒞 : Type)
                                                                 (_ : 
                                                                  axioms_ 𝒞),
                                                               Graph.axioms_ 𝒞 :=
  fun (𝒞 : Type) (c : axioms_ 𝒞) => Graph.Class 𝒞 (Category_IsGraph_mixin 𝒞 c).
Local Arguments Category_Category_class__to__Category_Graph_class : clear implicits.
Coercion Category_Category_class__to__Category_Graph_class : Category.Category.axioms_ >-> Category.Graph.axioms_.
Definition Category_Category__to__Category_Graph : forall _ : type, Graph.type :=
  fun s : type =>
  Graph.Pack (sort s)
    (Category_Category_class__to__Category_Graph_class (sort s) (class s)).
Local Arguments Category_Category__to__Category_Graph : clear implicits.
Coercion Category_Category__to__Category_Graph : Category.Category.type >-> Category.Graph.type.
Global Canonical Category_Category__to__Category_Graph.
Definition Category_Category_class__to__Category_Precategory_class : 
  forall (𝒞 : Type) (_ : axioms_ 𝒞), Precategory.axioms_ 𝒞 :=
  fun (𝒞 : Type) (c : axioms_ 𝒞) =>
  Precategory.Class 𝒞 (Category_IsGraph_mixin 𝒞 c)
    (Category_IsPrecategory_mixin 𝒞 c).
Local Arguments Category_Category_class__to__Category_Precategory_class : clear implicits.
Coercion Category_Category_class__to__Category_Precategory_class : Category.Category.axioms_ >-> Category.Precategory.axioms_.
Definition Category_Category__to__Category_Precategory : forall _ : type,
                                                         Precategory.type :=
  fun s : type =>
  Precategory.Pack (sort s)
    (Category_Category_class__to__Category_Precategory_class (sort s) (class s)).
Local Arguments Category_Category__to__Category_Precategory : clear implicits.
Coercion Category_Category__to__Category_Precategory : Category.Category.type >-> Category.Precategory.type.
Global Canonical Category_Category__to__Category_Precategory.
Coercion Category_IsGraph_mixin : Category.Category.axioms_ >-> Category.IsGraph.axioms_.
Coercion Category_IsPrecategory_mixin : Category.Category.axioms_ >-> Category.IsPrecategory.axioms_.
Coercion Category_IsCategory_mixin : Category.Category.axioms_ >-> Category.IsCategory.axioms_.
End Exports.
Import Exports.
Definition phant_on_ : forall (𝒞 : type) (_ : phant (sort 𝒞)), axioms_ (sort 𝒞) :=
  fun (𝒞 : type) (_ : phant (sort 𝒞)) => class 𝒞.
Local Arguments phant_on_ : clear implicits.
Notation on_ X1 := ( phant_on_ _ (Phant X1)).
Notation copy X2 X1 := ( phant_on_ _ (Phant X1) : axioms_ X2).
Notation on X1 := ( phant_on_ _ (Phant _) : axioms_ X1).
Module EtaAndMixinExports.
Section hb_instance_12.
Variable 𝒞 : type.
Local Arguments 𝒞 : clear implicits.
Definition HB_unnamed_factory_13 : axioms_ (@eta Type (sort 𝒞)) := class 𝒞.
Local Arguments HB_unnamed_factory_13 : clear implicits.
Definition Category_Category__to__Category_IsGraph : IsGraph.axioms_
                                                       (@eta Type
                                                          (Graph.sort
                                                             (Category_Category__to__Category_Graph
                                                                𝒞))) :=
  HB_unnamed_mixin_4 (Category_Category__to__Category_Graph 𝒞).
Local Arguments Category_Category__to__Category_IsGraph : clear implicits.
Definition Category_Category__to__Category_IsPrecategory : IsPrecategory.axioms_
                                                             (@eta Type
                                                                (Precategory.sort
                                                                   (Category_Category__to__Category_Precategory
                                                                    𝒞)))
                                                             (Precategory.Category_IsGraph_mixin
                                                                (@eta Type
                                                                   (Precategory.sort
                                                                    (Category_Category__to__Category_Precategory
                                                                    𝒞)))
                                                                (HB_unnamed_factory_7
                                                                   (Category_Category__to__Category_Precategory
                                                                    𝒞))) :=
  HB_unnamed_mixin_10 (Category_Category__to__Category_Precategory 𝒞).
Local Arguments Category_Category__to__Category_IsPrecategory : clear implicits.
Definition Category_Category__to__Category_IsCategory : IsCategory.axioms_
                                                          (@eta Type (sort 𝒞))
                                                          (Category_IsGraph_mixin
                                                             (@eta Type
                                                                (sort 𝒞))
                                                             HB_unnamed_factory_13)
                                                          (Category_IsPrecategory_mixin
                                                             (@eta Type
                                                                (sort 𝒞))
                                                             HB_unnamed_factory_13) :=
  Category_IsCategory_mixin (@eta Type (sort 𝒞)) HB_unnamed_factory_13.
Local Arguments Category_Category__to__Category_IsCategory : clear implicits.
Definition HB_unnamed_mixin_17 :=
  Category_IsCategory_mixin (@eta Type (sort 𝒞)) HB_unnamed_factory_13.
Local Arguments HB_unnamed_mixin_17 : clear implicits.
Definition structures_eta__canonical__Category_Category : type :=
  Pack (@eta Type (sort 𝒞))
    (Class (@eta Type (sort 𝒞))
       (HB_unnamed_mixin_4 (Category_Category__to__Category_Graph 𝒞))
       (HB_unnamed_mixin_10 (Category_Category__to__Category_Precategory 𝒞))
       HB_unnamed_mixin_17).
Local Arguments structures_eta__canonical__Category_Category : clear implicits.
Global Canonical structures_eta__canonical__Category_Category.
End hb_instance_12.
End EtaAndMixinExports.
End Category.
Export Category.Exports.
Export Category.EtaAndMixinExports.
Definition seqL : forall s : Category.type,
                  has_seqL (Category.sort s)
                    (@hom
                       (Graph.Pack (Category.sort s)
                          (Graph.Class (Category.sort s)
                             (Category.Category_IsGraph_mixin (Category.sort s)
                                (Category.class s)))))
                    (@idn
                       (Precategory.Pack (Category.sort s)
                          (Precategory.Class (Category.sort s)
                             (Category.Category_IsGraph_mixin (Category.sort s)
                                (Category.class s))
                             (Category.Category_IsPrecategory_mixin
                                (Category.sort s) (Category.class s)))))
                    (@seq
                       (Precategory.Pack (Category.sort s)
                          (Precategory.Class (Category.sort s)
                             (Category.Category_IsGraph_mixin (Category.sort s)
                                (Category.class s))
                             (Category.Category_IsPrecategory_mixin
                                (Category.sort s) (Category.class s))))) :=
  fun s : Category.type =>
  IsCategory.seqL (Category.sort s)
    (Category.Category_IsGraph_mixin (Category.sort s) (Category.class s))
    (Category.Category_IsPrecategory_mixin (Category.sort s) (Category.class s))
    (Category.Category_IsCategory_mixin (Category.sort s) (Category.class s)).
Local Arguments seqL : clear implicits.
Global Arguments seqL {_}.
Definition seqR : forall s : Category.type,
                  has_seqR (Category.sort s)
                    (@hom
                       (Graph.Pack (Category.sort s)
                          (Graph.Class (Category.sort s)
                             (Category.Category_IsGraph_mixin (Category.sort s)
                                (Category.class s)))))
                    (@idn
                       (Precategory.Pack (Category.sort s)
                          (Precategory.Class (Category.sort s)
                             (Category.Category_IsGraph_mixin (Category.sort s)
                                (Category.class s))
                             (Category.Category_IsPrecategory_mixin
                                (Category.sort s) (Category.class s)))))
                    (@seq
                       (Precategory.Pack (Category.sort s)
                          (Precategory.Class (Category.sort s)
                             (Category.Category_IsGraph_mixin (Category.sort s)
                                (Category.class s))
                             (Category.Category_IsPrecategory_mixin
                                (Category.sort s) (Category.class s))))) :=
  fun s : Category.type =>
  IsCategory.seqR (Category.sort s)
    (Category.Category_IsGraph_mixin (Category.sort s) (Category.class s))
    (Category.Category_IsPrecategory_mixin (Category.sort s) (Category.class s))
    (Category.Category_IsCategory_mixin (Category.sort s) (Category.class s)).
Local Arguments seqR : clear implicits.
Global Arguments seqR {_}.
Definition seqA : forall s : Category.type,
                  has_seqA (Category.sort s)
                    (@hom
                       (Graph.Pack (Category.sort s)
                          (Graph.Class (Category.sort s)
                             (Category.Category_IsGraph_mixin (Category.sort s)
                                (Category.class s)))))
                    (@seq
                       (Precategory.Pack (Category.sort s)
                          (Precategory.Class (Category.sort s)
                             (Category.Category_IsGraph_mixin (Category.sort s)
                                (Category.class s))
                             (Category.Category_IsPrecategory_mixin
                                (Category.sort s) (Category.class s))))) :=
  fun s : Category.type =>
  IsCategory.seqA (Category.sort s)
    (Category.Category_IsGraph_mixin (Category.sort s) (Category.class s))
    (Category.Category_IsPrecategory_mixin (Category.sort s) (Category.class s))
    (Category.Category_IsCategory_mixin (Category.sort s) (Category.class s)).
Local Arguments seqA : clear implicits.
Global Arguments seqA {_}.
Module ElpiOperations18.
End ElpiOperations18.
Export ElpiOperations18.
Notation Category X1 := ( Category.axioms_ X1).