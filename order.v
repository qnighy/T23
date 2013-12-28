Require Import ssreflect ssrfun ssrbool eqtype.
Require Import ssrnat seq choice.

Set Implicit Arguments.

Section ReflAntisymEqType.
  Variable T : Type.
  Variable Tle : rel T.
  Hypothesis Tle_reflexive : reflexive Tle.
  Hypothesis Tle_antisymmetric : antisymmetric Tle.
  Definition ReflAntisymEqMixin : Equality.mixin_of T.
    exists (fun x y => Tle x y && Tle y x).
    move=> x y; apply: (iffP idP) => [|<-].
    - by apply Tle_antisymmetric.
    - by rewrite Tle_reflexive.
  Defined.
End ReflAntisymEqType.

Module PartialOrder.
  Record mixin_of (T : Type) : Type := Mixin {
    op : rel T;
    le_reflexive : reflexive op;
    le_transitive : transitive op;
    le_antisymmetric : antisymmetric op
  }.

  Definition EqMixin T m :=
    ReflAntisymEqMixin
      (@le_reflexive T m)
      (@le_antisymmetric T m).

  Section ClassDef.
    Record class_of T := Class {
      base : Equality.class_of T;
      mixin : mixin_of T
    }.
    Local Coercion base : class_of >-> Equality.class_of.

    Structure type : Type := Pack {
      sort : Type;
      _ : class_of sort;
      _ : Type
    }.

    Local Coercion sort : type >-> Sortclass.
    Variables (T : Type) (cT : type).
    Definition class :=
      let: Pack _ c _ as cT' := cT
        return class_of cT' in
      c.
    Definition clone c of phant_id class c :=
      @Pack T c T.
    Let xT := let: Pack T _ _ := cT in T.
    Notation xclass := (class : class_of xT).

    Definition pack m :=
      fun bT b & phant_id (Equality.class bT) b =>
        Pack (@Class T b m).

    Definition eqType := @Equality.Pack cT xclass xT.
  End ClassDef.

  Module Exports.
    Coercion base : class_of >-> Equality.class_of.
    Coercion mixin : class_of >-> mixin_of.
    Coercion sort : type >-> Sortclass.
    Coercion eqType : type >-> Equality.type.
    Canonical eqType.
    Notation partialOrderType := type.
    Notation PartialOrderType T m := (@pack T m _ _ id).
    Notation PartialOrderMixin := Mixin.
    Notation "[ 'partialOrderType' 'of' T 'for' cT ]" := (@clone T cT _ idfun)
      (at level 0, format "[ 'partialOrderType' 'of' T 'for' cT ]")
      : form_scope.
    Notation "[ 'partialOrderType' 'of' T ]" := (@clone T _ _ id)
      (at level 0, format "[ 'partialOrderType' 'of' T ]")
      : form_scope.
  End Exports.
End PartialOrder.
Export PartialOrder.Exports.

Definition le_op T := PartialOrder.op (PartialOrder.class T).
Arguments le_op [T] _ _.

Definition lt_op(T:partialOrderType) : rel T :=
  fun x y => le_op x y && (x != y).
Arguments lt_op [T] _ _.

Delimit Scope order_scope with order.
Open Scope order_scope.

Notation "x <= y" := (le_op x y)
  (at level 70, no associativity) : order_scope.
Notation "x <= y :> T" := ((x : T) <= (y : T))%order
  (at level 70, y at next level) : order_scope.
Notation "x < y" := (lt_op x y)%order
  (at level 70, no associativity) : order_scope.
Notation "x < y :> T" := ((x : T) < (y : T))%order
  (at level 70, y at next level) : order_scope.

Notation "y >= x" := (x <= y)
  (at level 70, no associativity, only parsing) : order_scope.
Notation "y >= x :> T" := (x <= y :> T)
  (at level 70, x at next level, only parsing) : order_scope.
Notation "y > x" := (x < y)
  (at level 70, no associativity, only parsing) : order_scope.
Notation "y > x :> T" := (x < y :> T)
  (at level 70, x at next level, only parsing) : order_scope.

Lemma le_refl(T : partialOrderType) : reflexive (@le_op T).
Proof.
  by apply: PartialOrder.le_reflexive.
Qed.
Lemma le_trans(T : partialOrderType) : transitive (@le_op T).
Proof.
  by apply: PartialOrder.le_transitive.
Qed.
Lemma le_antisym(T : partialOrderType) : antisymmetric (@le_op T).
Proof.
  by apply: PartialOrder.le_antisymmetric.
Qed.
Lemma le_antisym_rewrite(T : partialOrderType) (x y : T):
  ((x <= y) && (y <= x)) = (x == y).
Proof.
  apply: sameP; [|apply idP].
  apply: (iffP idP) => [H|].
  - apply/eqP.
    by move: H; apply le_antisym.
  - move=> /eqP <-.
    by rewrite le_refl.
Qed.


Module TotalOrder.
  Record mixin_of (T : Type) (op : rel T) : Type := Mixin {
    le_reflexive : reflexive op;
    le_transitive : transitive op;
    le_antisymmetric : antisymmetric op;
    le_total : total op
  }.

  Definition PartialOrderMixin T (op : rel T) (m:mixin_of op) := {|
    PartialOrder.op := op;
    PartialOrder.le_reflexive := le_reflexive m;
    PartialOrder.le_transitive := le_transitive m;
    PartialOrder.le_antisymmetric := le_antisymmetric m
  |}.
    
  Definition EqMixin T (op : rel T) (m:mixin_of op) := 
    PartialOrder.EqMixin (PartialOrderMixin m).

  Section ClassDef.
    Record class_of T := Class {
      base : PartialOrder.class_of T;
      mixin : mixin_of (PartialOrder.op base)
    }.
    Local Coercion base : class_of >-> PartialOrder.class_of.

    Structure type : Type := Pack {
      sort : Type;
      _ : class_of sort;
      _ : Type
    }.

    Local Coercion sort : type >-> Sortclass.
    Variables (T : Type) (cT : type).
    Definition class :=
      let: Pack _ c _ as cT' := cT
        return class_of cT' in
      c.
    Definition clone c of phant_id class c :=
      @Pack T c T.
    Let xT := let: Pack T _ _ := cT in T.
    Notation xclass := (class : class_of xT).

    Definition eqType := @Equality.Pack cT xclass xT.
    Definition partialOrderType := @PartialOrder.Pack cT xclass xT.
  End ClassDef.

  Module Exports.
    Coercion base : class_of >-> PartialOrder.class_of.
    Coercion mixin : class_of >-> mixin_of.
    Coercion sort : type >-> Sortclass.
    Coercion eqType : type >-> Equality.type.
    Canonical eqType.
    Coercion partialOrderType : type >-> PartialOrder.type.
    Canonical partialOrderType.
    Notation totalOrderType := type.
    Notation TotalOrderMixin := Mixin.
    Notation "[ 'totalOrderType' 'of' T 'for' cT ]" := (@clone T cT _ idfun)
      (at level 0, format "[ 'totalOrderType' 'of' T 'for' cT ]")
      : form_scope.
    Notation "[ 'totalOrderType' 'of' T ]" := (@clone T _ _ id)
      (at level 0, format "[ 'totalOrderType' 'of' T ]")
      : form_scope.
  End Exports.
End TotalOrder.
Export TotalOrder.Exports.

Lemma le_total(T : totalOrderType) : total (@le_op T).
Proof.
  apply: TotalOrder.le_total.
  apply: TotalOrder.mixin.
Qed.

CoInductive compare2_spec(T:totalOrderType) (x y:T) :
    bool -> bool -> Set :=
  | Compare2Le of x <= y : compare2_spec T x y true false
  | Compare2Gt of x > y : compare2_spec T x y false true.

Lemma compare2P(T:totalOrderType) (x y:T) :
    compare2_spec T x y (x <= y) (x > y).
Proof.
  case le_xy: (x <= y) => /=.
  - rewrite (_:y < x = false).
    - by apply Compare2Le.
    - unfold lt_op.
      case le_yx: (y <= x) => /=; last done.
      move: {le_xy le_yx} (conj le_xy le_yx) => /andP /le_antisym <-.
      by rewrite eq_refl.
  - have: y < x.
    - unfold lt_op.
      case/orP: (le_total T x y) le_xy => -> // le_xy /=.
      case eq_yx: (y == x); last done.
      by move: eq_yx (le_refl T x) le_xy => /eqP -> ->.
    - move=> lt_yx.
      rewrite lt_yx.
      by apply Compare2Gt.
Qed.

CoInductive compare3_spec(T:totalOrderType) (x y:T) :
    bool -> bool -> bool -> Set :=
  | Compare3Lt of x < y : compare3_spec T x y true false false
  | Compare3Eq of x == y : compare3_spec T x y false true false
  | Compare3Gt of x > y : compare3_spec T x y false false true.

Lemma compare3P(T:totalOrderType) (x y:T) :
    compare3_spec T x y (x < y) (x == y) (x > y).
Proof.
  rewrite -(le_antisym_rewrite T x y).
  case: (compare2P T x y) => [le_xy|lt_yx];
    case: (compare2P T y x) => [le_yx|lt_xy] /=.
  - by apply Compare3Eq; rewrite -(le_antisym_rewrite T x y) le_xy le_yx.
  - by apply Compare3Lt.
  - by apply Compare3Gt.
  - move: lt_yx lt_xy => /andP [le_xy _] /andP [le_yx].
    by rewrite -le_antisym_rewrite le_xy le_yx.
Qed.