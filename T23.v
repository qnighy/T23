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

Module TotalOrder.
  Record mixin_of (T : Type) : Type := Mixin {
    op : rel T;
    le_reflexive : reflexive op;
    le_transitive : transitive op;
    le_antisymmetric : antisymmetric op;
    le_total : total op
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
    Notation totalOrderType := type.
    Notation TotalOrderType T m := (@pack T m _ _ id).
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

Definition le_op T := TotalOrder.op (TotalOrder.class T).

Arguments le_op [T] _ _.

Delimit Scope total_order_scope with total_order.

Notation "x <= y" := (le_op x y)
  (at level 70, no associativity) : total_order_scope.
Notation "x <= y :> T" := ((x : T) <= (y : T))%total_order
  (at level 70, y at next level) : total_order_scope.
Notation "y < x" := (~~ (x <= y))%total_order
  (at level 70, no associativity) : total_order_scope.
Notation "y < x :> T" := (~~ ((x : T) <= (y : T)))%total_order
  (at level 70, x at next level) : total_order_scope.


Local Open Scope total_order_scope.

CoInductive compare3_spec(T:totalOrderType) (x y:T) :
    bool -> bool -> bool -> Set :=
  | Compare3Lt of x < y : compare3_spec T x y true false false
  | Compare3Gt of y < x : compare3_spec T x y false true false
  | Compare3Eq of x == y : compare3_spec T x y false false true.

Section Def.
  Variable TK : totalOrderType.
  Variable TV : eqType.
  Inductive tree : Type :=
    | empty : tree
    | node2 of tree & TK * TV & tree
    | node3 of tree & TK * TV & tree & TK * TV & tree.

  Fixpoint eqn t0 t1 { struct t0 } :=
    match t0,t1 with
    | empty, empty => true
    | node2 t0s0 t0e0 t0s1, node2 t1s0 t1e0 t1s1 =>
      [&& eqn t0s0 t1s0, (t0e0 == t1e0) & eqn t0s1 t1s1]
    | node3 t0s0 t0e0 t0s1 t0e1 t0s2,
      node3 t1s0 t1e0 t1s1 t1e1 t1s2 =>
      [&& eqn t0s0 t1s0, (t0e0 == t1e0),
          eqn t0s1 t1s1, (t0e1 == t1e1) & eqn t0s2 t1s2]
    | _,_ => false
    end.

  Lemma eqnP : Equality.axiom eqn.
  Proof.
    move=> t0 t1; apply: (iffP idP)=> [|<- {t1}].
    - elim: t0 t1 => [|t0s0 Hs0 t0e0 t0s1 Hs1
                      |t0s0 Hs0 t0e0 t0s1 Hs1 t0e1 t0s2 Hs2].
      - by case.
      - by case=> // t1s0 t1e0 t1s1 /=
                  /and3P [/Hs0<- /eqP<- /Hs1<-].
      - by case=> // t1s0 t1e0 t1s1 t1e1 t1s2 /=
                  /and5P [/Hs0<- /eqP<- /Hs1<- /eqP<- /Hs2<-].
    - elim: t0 => /= [|t0s0 -> t0e0 t0s1 ->
                      |t0s0 -> t0e0 t0s1 -> t0e1 t0s2 ->].
      - done.
      - by rewrite eq_refl.
      - by rewrite eq_refl eq_refl.
  Qed.

  Canonical tree_eqMixin := EqMixin eqnP.
  Canonical tree_eqType := Eval hnf in EqType tree tree_eqMixin.

  Fixpoint tree_check_ordered(t:tree) (lb ub:option TK) : bool :=
    match t with
    | empty =>
      match lb,ub with
      | Some lbs, Some ubs => lbs <= ubs
      | _, _ => true
      end
    | node2 t0 (k0,v0) t1 =>
      tree_check_ordered t0 lb (Some k0) &&
      tree_check_ordered t1 (Some k0) ub
    | node3 t0 (k0,v0) t1 (k1,v1) t2 =>
      [&& tree_check_ordered t0 lb (Some k0),
          tree_check_ordered t1 (Some k0) (Some k1) &
          tree_check_ordered t2 (Some k1) ub]
    end.

  Fixpoint tree_depth(t:tree) : nat :=
    match t with
    | empty => 0
    | node2 t0 _ t1 => (maxn (tree_depth t0) (tree_depth t1)) .+1
    | node3 t0 _ t1 _ t2 =>
      (maxn (tree_depth t0) (maxn (tree_depth t1) (tree_depth t2))) .+1
    end.

  Fixpoint tree_check_depth(t:tree) : bool :=
    match t with
    | empty => true
    | node2 t0 _ t1 =>
      [&& (tree_depth t0 == tree_depth t1),
          tree_check_depth t0 & tree_check_depth t1]
    | node3 t0 _ t1 _ t2 =>
      [&& (tree_depth t0 == tree_depth t1), (tree_depth t1 == tree_depth t2),
          tree_check_depth t0, tree_check_depth t1 & tree_check_depth t2]
    end.

  Definition tree_valid(t:tree) : bool :=
    tree_check_ordered t None None && tree_check_depth t.

  Definition T23 := sig tree_valid.

  Definition tree_append(k:TK) (v:TV):tree -> bool*tree :=
    fix recur(t:tree) :=
    match t with
    | empty => (true, node2 empty (k,v) empty)
    | node2 t0 ((k0,_) as e0) t1 =>
      if k < k0 then
        match recur t0 with
        | (true, node2 s0 se0 s1) =>
          (false, node3 s0 se0 s1 e0 t1)
        | (_, s) => (false, node2 s e0 t1)
        end
      else if k == k0 then
        (false, node2 t0 (k,v) t1)
      else
        match recur t1 with
        | (true, node2 s0 se0 s1) =>
          (false, node3 t0 e0 s0 se0 s1)
        | (_, s) => (false, node2 t0 e0 s)
        end
    | node3 t0 ((k0,_) as e0) t1 ((k1,_) as e1) t2 =>
      if k < k0 then
        match recur t0 with
        | (true, s) =>
          (true, node2 s e0 (node2 t1 e1 t2))
        | (_, s) => (false, node3 s e0 t1 e1 t2)
        end
      else if k == k0 then
        (false, node3 t0 (k,v) t1 e1 t2)
      else if k < k1 then
        match recur t1 with
        | (true, node2 s0 se0 s1) =>
          (true, node2 (node2 t0 e0 s0) se0 (node2 s1 e1 t2))
        | (_, s) => (false, node3 t0 e0 s e1 t2)
        end
      else if k == k1 then
        (false, node3 t0 e0 t1 (k,v) t2)
      else
        match recur t2 with
        | (true, s) =>
          (true, node2 (node2 t0 e0 t1) e1 s)
        | (_, s) => (false, node3 t0 e0 t1 e1 s)
        end
    end.

  Lemma tree_append_preserve_depth(t:tree) (k:TK) (v:TV):
    let (r,t') := tree_append k v t in
    tree_depth t' =
      if r then (tree_depth t) .+1 else tree_depth t.
  Proof.
    elim: t => [|t0 Ht0 [k0 v0] t1 Ht1|] /=.
    - done.
    - de
    -
  Qed.
End Def.