Require Import ssreflect ssrfun ssrbool eqtype.
Require Import ssrnat seq choice.
Require Import order.

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
      | Some lbs, Some ubs => lbs < ubs
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
          tree_check_depth t0 & nosimpl tree_check_depth t1]
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
    (tree_depth t' =
      if r then (tree_depth t) .+1 else tree_depth t) /\
    match r,t' with
    | false,_ => true
    | _,node2 _ _ _ => true
    | _,_ => false
    end.
  Proof.
    elim: t => [|t0 Ht0 [k0 v0] t1 Ht1
                |t0 Ht0 [k0 v0] t1 Ht1 [k1 v1] t2 Ht2] /=.
    - done.
    - case: (compare3P TK k k0) => Hk.
      - case: (tree_append k v t0) Ht0 => [[|] s].
        - case: s => [|s0 se0 s1|s se0 s1 se1 s2] /= [[Ht0]] // _.
          by rewrite maxnA Ht0.
        - by move=> [<- _].
      - done.
      - case: (tree_append k v t1) Ht1 => [[|] s].
        - case: s => [|s0 se0 s1|s se0 s1 se1 s2] /= [[Ht1]] // _.
          by rewrite Ht1.
        - by move=> [<- _].
    - case: (compare3P TK k k0) => Hk0;
          [| |case: (compare3P TK k k1) => Hk1].
      - case: (tree_append k v t0) Ht0 => [[|] s].
        - case: s => [|s0 se0 s1|s se0 s1 se1 s2] /= [[Ht0]] // _.
          by rewrite maxnSS Ht0.
        - by move=> [<- _].
      - done.
      - case: (tree_append k v t1) Ht1 => [[|] s].
        - case: s => [|s0 se0 s1|s se0 s1 se1 s2] /= [[Ht1]] // _.
          by rewrite maxnSS -maxnA (maxnA (tree_depth s0)) Ht1.
        - by move=> [<- _].
      - done.
      - case: (tree_append k v t2) Ht2 => [[|] s].
        - case: s => [|s0 se0 s1|s se0 s1 se1 s2] /= [[Ht2]] // _.
          by rewrite maxnSS -maxnA Ht2.
        - by move=> [<- _].
  Qed.

  Lemma maxn_eq m : maxn m m = m.
  Proof.
    by unfold maxn; case (m < m)%N.
  Qed.

  Lemma tree_append_preserves_depth_validity(t:tree) (k:TK) (v:TV):
      tree_check_depth t -> tree_check_depth (tree_append k v t).2.
  Proof.
    elim: t => [|t0 Ht0 [k0 v0] t1 Ht1
                |t0 Ht0 [k0 v0] t1 Ht1 [k1 v1] t2 Ht2] /=.
    - done.
    - case: (compare3P TK k k0) => Hk.
      - case: (tree_append k v t0)
              (tree_append_preserve_depth t0 k v) Ht0 => [[|] s].
        - case: s => [|s0 se0 s1|s se0 s1 se1 s2] /= [[Hpd]] // _ Ht0A Ht0B.
          move: Ht0B Hpd => /and3P [/eqP<- /Ht0A/and3P[/eqP<- -> ->] ->] <-.
          by rewrite maxn_eq eq_refl.
        - by move=> /= [-> _] Ht0 /and3P [-> /Ht0-> ->].
      - done.
      - case: (tree_append k v t1)
              (tree_append_preserve_depth t1 k v) Ht1 => [[|] s].
        - case: s => [|s0 se0 s1|s se0 s1 se1 s2] /= [[Hpd]] // _ Ht1A Ht1B.
          move: Ht1B Hpd => /and3P [/eqP<- ->/Ht1A/and3P[/eqP<- -> ->]] <-.
          by rewrite maxn_eq eq_refl.
        - by move=> /= [-> _] Ht1 /and3P [-> -> /Ht1->].
    - case: (compare3P TK k k0) => Hk0;
          [| |case: (compare3P TK k k1) => Hk1].
      - case: (tree_append k v t0)
              (tree_append_preserve_depth t0 k v) Ht0 => [[|] s].
        - case: s => [|s0 se0 s1|s se0 s1 se1 s2] /= [[Hpd]] // _ Ht0A Ht0B.
          move: Ht0B Hpd =>
              /and5P[/eqP-> /eqP<- /Ht0A/and3P[/eqP<- -> ->] -> ->] ->.
          by rewrite maxn_eq eq_refl eq_refl eq_refl.
        - by move=> /= [-> _] Ht0 /and5P[-> -> /Ht0-> -> ->].
      - done.
      - case: (tree_append k v t1)
              (tree_append_preserve_depth t1 k v) Ht1 => [[|] s].
        - case: s => [|s0 se0 s1|s se0 s1 se1 s2] /= [[Hpd]] // _ Ht1A Ht1B.
          move: Ht1B Hpd =>
              /and5P[/eqP-> /eqP<- -> /Ht1A/and3P[/eqP<- -> ->] ->].
          rewrite maxn_eq=> <-.
          by rewrite eq_refl eq_refl.
        - by move=> /= [-> _] Ht1 /and5P[-> -> -> /Ht1-> ->].
      - done.
      - case: (tree_append k v t2)
              (tree_append_preserve_depth t2 k v) Ht2 => [[|] s].
        - case: s => [|s0 se0 s1|s se0 s1 se1 s2] /= [[Hpd]] // _ Ht2A Ht2B.
          move: Ht2B Hpd =>
              /and5P[/eqP-> /eqP<- -> -> /Ht2A/and3P[/eqP<- -> ->]] ->.
          by rewrite maxn_eq eq_refl eq_refl eq_refl.
        - by move=> /= [-> _] Ht2 /and5P[-> -> -> -> /Ht2->].
  Qed.
  Lemma tree_append_preserves_order_validity(t:tree)
      (k:TK) (v:TV) (lb ub:option TK):
      (if lb is Some lbs then lbs < k else true) ->
      (if ub is Some ubs then k < ubs else true) ->
      tree_check_ordered t lb ub -> tree_check_ordered (tree_append k v t).2 lb ub.
  Proof.
    elim: t lb ub => [|t0 Ht0 [k0 v0] t1 Ht1
                |t0 Ht0 [k0 v0] t1 Ht1 [k1 v1] t2 Ht2] /=.
    - by move=> lb ub -> -> _.
    - case: (compare3P TK k k0) => Hk.
      - case: (tree_append k v t0) Ht0
            => [[|] [|s0 [sk0 sv0] s1|s [sk0 sv0] s1 [sk1 sv1] s2]]
               /= Ht0A lb ub Hlb Hub /andP[Ht0B ->];
          try by rewrite (Ht0A lb (Some k0) Hlb Hk Ht0B).
        by rewrite Bool.andb_true_r Ht0A.
      - by move: Hk => /eqP<-.
      - by case: (tree_append k v t1) Ht1
               => [[|] [|s0 [sk0 sv0] s1|s [sk0 sv0] s1 [sk1 sv1] s2]]
                  /= Ht1A lb ub Hlb Hub /andP[-> Ht1B];
           rewrite (Ht1A _ _ _ Hub Ht1B).
    - case: (compare3P TK k k0) => Hk0;
          [| |case: (compare3P TK k k1) => Hk1].
      - by case: (tree_append k v t0) Ht0
               => [[|] [|s0 se0 s1|s se0 s1 se1 s2]]
                  /= Ht0A lb ub Hlb Hub /and3P[Ht0B -> ->];
           rewrite (Ht0A _ _ Hlb _ Ht0B).
      - by move: Hk0 => /eqP<-.
      - case: (tree_append k v t1) Ht1
            => [[|] [|s0 [sk0 sv0] s1|s [sk0 sv0] s1 [sk1 sv1] s2]]
                     /= Ht1A lb ub Hlb Hub /and3P[-> Ht1B ->];
          try by move: (Ht1A (Some k0) (Some k1) Hk0 Hk1 Ht1B)=> /andP [-> ->].
        - by rewrite (lt_trans _ _ _ _ Hk0 Hk1).
        - by rewrite (lt_trans _ _ _ _ Hk0 Hk1).
      - by move: Hk1 => /eqP<-.
      - by case: (tree_append k v t2) Ht2
               => [[|] [|s0 se0 s1|s se0 s1 se1 s2]]
                  /= Ht2A lb ub Hlb Hub /and3P[-> -> Ht2B];
           rewrite (Ht2A _ _ _ Hub Ht2B).
  Qed.
End Def.